{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
{-# OPTIONS -Wall #-}
module Tig5
  ( NonTerminal(..)
  , Node(..)
  , Tree(..), mkTree, showTree
  , TIG, mkTIG, showTIG
  , parse
  -- Node makers
  , footN, termTree, termTreeN, mkTreeN, ntN
  ) where

-- ==============================================================================
-- ==============================================================================
--  Tree Insertion Grammar recognizer and parser
--  Original Python version By Tomer Filiba, 2012-04-28
--  Based on an algorithm outlined in [Schabes 94]
--
--  Transliterated to Haskell by Eyal Lotem, 2013.
-- ==============================================================================
-- ==============================================================================

import Control.Lens (makeLenses, makePrisms, ix, traverse, both)
import Control.Lens.Operators
import Control.Monad (join, forM_, when)
import Control.Monad.Trans.State.Strict (State, execState)
import Data.Either (partitionEithers)
import Data.Function (on)
import Data.Map (Map, (!))
import Data.Maybe (fromMaybe)
import Data.Monoid (mconcat)
import Data.Set (Set)
import Data.Typeable (Typeable)
import StrictStateAPI
import Text.Printf.Mauke.TH
import qualified Control.Exception as E
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

--  Whether or not to use unicode (some terminals choke on this)
data Symbols = Symbols { symDownArrow, symRightArrow, symDot :: String }
_unicodeSymbols :: Symbols
_unicodeSymbols = Symbols "↓" "→" "·"
_nonUnicodeSymbols :: Symbols
_nonUnicodeSymbols = Symbols "^" "->" "@"

symbols :: Symbols
symbols = _nonUnicodeSymbols

-- ==============================================================================
--  Exceptions
-- ==============================================================================
data GrammarError = GrammarError String deriving (Show, Typeable) -- Raised when constructing the TIG
instance E.Exception GrammarError
data ParsingError = ParsingError String deriving (Show, Typeable) -- Raised when parsing fails
instance E.Exception ParsingError
data AssertionError = AssertionError String deriving (Show, Typeable)
instance E.Exception AssertionError

-- ==============================================================================
--  Building Blocks
-- ==============================================================================

-- | Represents a non-terminal in the grammar; there's no need for a
-- class to represent terminals, as we just use strings for that
data NonTerminal = NonTerminal { ntName :: String }
    deriving (Show, Eq, Ord)

data Node
    = NodeTerminal String
    | NodeNonTerminal NonTerminal
    | NodeFoot NonTerminal
    | NodeTree Tree
    deriving (Show, Eq, Ord)

data TreeType = InitTree | LeftAux | RightAux | DerivationTree
    deriving (Show, Eq, Ord)

-- | Represents a grammar tree. This could be either an initial,
-- left-aux or right-aux tree, or a deviation tree (we reuse this
-- class for this purpose too). Note that trees compare by *value*,
-- not identity, and are immutable once created.
data Tree = Tree
  { _treeType :: TreeType
  , _treeRoot :: NonTerminal
  , _treeChildren :: [Node]
  } deriving (Eq, Ord, Show)

-- | Represents a TIG grammar instance; it basically holds the initial and
-- auxiliary trees that make up the grammar. Upon creation, this class
-- verifies the given trees indeed form a valid TIG.
data TIG = TIG
  { tigInitTreesBySymbol :: Map NonTerminal [Tree]
  , tigLeftAuxTreesBySymbol :: Map NonTerminal [Tree]
  , tigRightAuxTreesBySymbol :: Map NonTerminal [Tree]
  } deriving (Show)

-- ==============================================================================
--  Chart and Chart States
-- ==============================================================================

-- | The chart state. This is in essence a 4-tuple <tree, dot, i, j>, with some
-- helper methods
data ChartState = ChartState
  { csTree :: Tree, csDot :: Int, csI :: Int, csJ :: Int }
  deriving (Eq, Ord, Show)

type Reason = String
data SubtreeFunc = SubtreeFunc
  { sFunc :: Chart -> [Tree]
  , sName :: String
  }
instance Eq SubtreeFunc where (==) = (==) `on` sName
instance Ord SubtreeFunc where compare = compare `on` sName
instance Show SubtreeFunc where show = sName

-- | A helper object, associated with each chart state, that holds the
-- reasons for adding this state and the state's subtree builders
data ChartItem = ChartItem
  { _ciReasons :: Set Reason
  , _ciSubtreeFuncs :: Set SubtreeFunc
  }
instance Show ChartItem where
  show (ChartItem reasons subtreeFuncs) =
    show (Set.toList reasons) ++ ", " ++ show subtreeFuncs

-- | Represents the parser chart. It comprises of states (without duplicates),
-- but it preserves the ordering relations for debugging purposes. With each
-- state we associates a ChartItem, to hold some extra info.
-- States are add()ed to the chart, but they don't actually become part of
-- it until commit()ted. This prevents some issues with dictionary iteration.
data Chart = Chart
  { __chartStates :: Map ChartState ChartItem
  , _chartOrderedStates :: [ChartState]
  , _chartChanges :: [(ChartState, Reason, SubtreeFunc)]
  }

makeLenses ''ChartItem
makeLenses ''Chart
makeLenses ''Tree
makePrisms ''Node

mkTree :: NonTerminal -> [Node] -> Tree
mkTree = Tree InitTree

footN :: NonTerminal -> Node
footN = NodeFoot

termTree :: NonTerminal -> String -> Tree
termTree nt str = mkTree nt [NodeTerminal str]

termTreeN :: NonTerminal -> String -> Node
termTreeN nt str = NodeTree $ termTree nt str

mkTreeN :: NonTerminal -> [Node] -> Node
mkTreeN nt children = NodeTree $ mkTree nt children

ntN :: NonTerminal -> Node
ntN = NodeNonTerminal

strNode :: Node -> String
strNode (NodeTerminal x) = x
strNode (NodeNonTerminal x) = ntName x
strNode (NodeFoot x) = ntName x ++ "*"
strNode (NodeTree x) = strTree x

strTree :: Tree -> String
strTree (Tree _ root children) =
  ntName root ++ "(" ++ List.intercalate ", " (map strNode children) ++ ")"

enumerate :: [a] -> [(Int, a)]
enumerate = zip [0..]

pathToFoot :: Tree -> Maybe [Int]
pathToFoot (Tree _ _ children) = loop $ enumerate children
  where
    loop [] = Nothing
    loop ((i, node) : rest) = maybe (loop rest) (Just . (i:)) $ nodePathToFoot node
    nodePathToFoot (NodeFoot _) = Just []
    nodePathToFoot (NodeTree x) = pathToFoot x
    nodePathToFoot _ = Nothing

modifyTree :: (Tree -> Tree) -> Tree -> Tree
modifyTree f = (treeType .~ DerivationTree) . f

substitute :: Int -> Node -> Tree -> Tree
substitute i child = modifyTree (treeChildren . ix i .~ child)

-- | Returns a copy of this tree, in which the i'th child is replaced by
-- the given subtree. If this tree contains a foot, substitution occurs
-- in the i'th child of the parent of the foot instead
deepSubstitute :: Int -> Node -> Tree -> Tree
deepSubstitute i child rootTree =
  case pathToFoot rootTree of
  Nothing -> substitute i child rootTree
  Just path -> loop (init path) rootTree
  where
    loop [] = substitute i child
    loop (p:ps) = modifyTree (treeChildren . ix p . _NodeTree %~ loop ps)

-- | Returns a copy of this tree, in which the foot (should it exist) is
-- replaced by the given subtree
substituteFoot :: Tree -> Tree -> Tree
substituteFoot subtree = modifyTree (treeChildren . traverse %~ f)
  where
    f (NodeFoot _) = NodeTree subtree
    f (NodeTree x) = NodeTree $ substituteFoot subtree x
    f other = other

-- | returns an iterator over the non-empty leaves of this tree
treeLeaves :: Tree -> [Node]
treeLeaves (Tree _ _ children) = concatMap nodeLeaves children
  where
    nodeLeaves (NodeTree x) = treeLeaves x
    nodeLeaves (NodeTerminal "") = [] -- ignore epsilon productions in leaves:
    nodeLeaves other = [other]

fromlines :: [String] -> String
fromlines = List.intercalate "\n"

indent :: Int -> String -> String
indent n = fromlines . map (prefix ++) . lines
  where
    prefix = replicate n ' '

-- | Prints the tree in a human-readable manner
showTree :: Tree -> String
showTree = showTreeLevel 0
  where
    prefix level = replicate (3 * level) ' '
    showTreeLevel level (Tree _ root children) =
      fromlines $
      (prefix level ++ ntName root) :
      map (showNode (level+1)) children
    showNode level (NodeTree x) = showTreeLevel level x
    showNode level other = prefix level ++ strNode other

showTIG :: TIG -> String
showTIG (TIG inits lefts rights) = fromlines . concat $
  [ showMap "inits" inits
  , showMap "lefts" lefts
  , showMap "rights" rights
  ]
  where
    showMap title m =
      ( "===" ++ title ++ "===" ) :
      concatMap showPair (Map.toList m)
    showPair (nt, ts) =
      ( ntName nt ++ " -> " ) :
      map (indent 3 . showTree) (List.sort ts)

assert :: E.Exception e => e -> (a -> Bool) -> a -> a
assert err p x
  | p x = x
  | otherwise = E.throw err

mkTIG :: [Tree] -> [Tree] -> TIG
mkTIG initTrees rawAuxTrees =
  TIG initTreesBySym leftAuxTreesBySym rightAuxTreesBySym
  where
    mkMap = fmap List.sort . Map.fromListWith (++) . map (\t -> (t ^. treeRoot, [t]))
    initTreesBySym = mkMap $ map eachInitTree initTrees
    verifyTreeLeaves n =
      assert (GrammarError ("trees must contain " ++ show n ++ "foot leaves"))
        ((== n) . length . filter isFoot) .
      assert (GrammarError "trees must not be empty") (not . null) .
      treeLeaves
    eachInitTree t = verifyTreeLeaves 0 t `seq` t
    isFoot (NodeFoot _) = True
    isFoot _ = False
    (leftAuxTreesBySym, rightAuxTreesBySym) =
      (both %~ mkMap) . partitionEithers $ map eachAuxTree rawAuxTrees
    eachAuxTree t = decideAuxSide t $ verifyTreeLeaves 1 t
    decideAuxSide t ls =
      snd .
      assert
      (GrammarError
       ("The foot of an auxiliary tree must be of " ++
        "the same nonterminal as the root"))
      ((== t ^. treeRoot) . fst) $
      case (head ls, last ls) of
      (_, NodeFoot nt) -> (nt, Left (t & treeType .~ LeftAux))
      (NodeFoot nt, _) -> (nt, Right (t & treeType .~ RightAux))
      _ -> E.throw . GrammarError $
           "Auxiliary trees must contain either a " ++
           "leftmost or a rightmost foot: " ++ show t

-- | Returns a (possibly empty) list of initial trees whose roots are the
-- given non-terminal
getInitTreesFor :: NonTerminal -> TIG -> [Tree]
getInitTreesFor symbol = List.sort . fromMaybe [] . Map.lookup symbol . tigInitTreesBySymbol

-- | Returns a (possibly empty) list of left-auxiliary trees whose roots
-- are the given non-terminal
getLeftAuxTreesFor :: NonTerminal -> TIG -> [Tree]
getLeftAuxTreesFor symbol = List.sort . fromMaybe [] . Map.lookup symbol . tigLeftAuxTreesBySymbol

-- | Returns a (possibly empty) list of right-auxiliary trees whose roots
-- are the given non-terminal
getRightAuxTreesFor :: NonTerminal -> TIG -> [Tree]
getRightAuxTreesFor symbol = List.sort . fromMaybe [] . Map.lookup symbol . tigRightAuxTreesBySymbol

insertAt :: Int -> a -> [a] -> [a]
insertAt 0 new xs = new:xs
insertAt n new (x:xs)
  | n > 0 = x : insertAt (n-1) new xs
  | otherwise = error "Negative index to insertAt"
insertAt _ _ [] = error "Too-large index to insertAt"

strState :: ChartState -> String
strState (ChartState tree dot i j) =
  unwords [ntName (tree ^. treeRoot), symRightArrow symbols, prod] ++
  ",  " ++ show i ++ ":" ++ show j
  where
    prod =
      unwords . insertAt dot (symDot symbols) . map onChild $
      tree ^. treeChildren
    onChild c = strNode c ++ childSuffix c
    childSuffix NodeNonTerminal{} = symDownArrow symbols
    childSuffix _ = ""

-- | the dot is past the last child (thus the state is complete)
csIsComplete :: ChartState -> Bool
csIsComplete (ChartState tree dot _ _) =
  dot >= length (tree ^. treeChildren)

-- | Return the next (first-level only) production of this tree,
-- or None if we've reached the end
nextProduction :: ChartState -> Maybe Node
nextProduction st@(ChartState tree dot _ _)
  | csIsComplete st = Nothing
  | otherwise = Just $ (tree ^. treeChildren) !! dot

mkChartItem :: Reason -> SubtreeFunc -> ChartItem
mkChartItem reason subtreeFunc = ChartItem
  { _ciReasons = Set.singleton reason
  , _ciSubtreeFuncs = Set.singleton subtreeFunc
  }

-- | Adds a reason and a subtree-builder to this chart item
chartItemAdd :: Reason -> SubtreeFunc -> ChartItem -> ChartItem
chartItemAdd reason subtreeFunc chartItem =
  chartItem
  & ciReasons <>~ Set.singleton reason
  & ciSubtreeFuncs %~ Set.insert subtreeFunc

emptyChart :: Chart
emptyChart = Chart Map.empty [] []

-- | Adds a new state to the chart, including the state's reason and
-- subtree-builder. Note that it's not actually added to the chart
-- until commit() is called
chartAdd :: ChartState -> Reason -> Maybe SubtreeFunc -> State Chart ()
chartAdd st reason mSubtreeFunc =
  chartChanges <>= [(st, reason, subTreeFunc)]
  where
    subTreeFunc = fromMaybe (SubtreeFunc (const [csTree st]) ("BUILD_CONST: " ++ strState st)) mSubtreeFunc

-- | commits the changes to the chart -- returns True if the chart
-- has grew, False otherwise
commit :: Chart -> (Bool, Chart)
commit = loop False
  where
    loop added chart@(Chart _ _ []) = (added, chart)
    loop added (Chart states ordered ((st, reason, subtreeFunc):changes)) =
      case Map.lookup st states of
      Nothing ->
        loop True $
        Chart (Map.insert st (mkChartItem reason subtreeFunc) states)
        (ordered ++ [st]) changes
      Just chartItem ->
        loop added $
        Chart (Map.insert st (chartItemAdd reason subtreeFunc chartItem) states)
        ordered changes

-- | Gets the set of subtrees for a given state; this is memoized (cached)
-- so once the subtrees of some state have been built,
-- future calls are O(1)
getSubtrees :: ChartState -> Chart -> Set Tree
getSubtrees st chart@(Chart states _ _) =
  mconcat . map (Set.fromList . ($ chart) . sFunc) . Set.toList $ item ^. ciSubtreeFuncs
  where
    item = states ! st

-- | Print the chart in a human-readable manner
_showChart :: Bool -> Chart -> String
_showChart onlyCompleted (Chart states rawOrdered _) = fromlines $
  [ $(printf "%3d | %-40s | %s") index (strState st)
    (List.intercalate " ; " (Set.toList ((states ! st) ^. ciReasons)))
  | (index, st) <- ordered
  ] ++
  [ replicate 80 '-' ]
  where
    maybeOnlyCompleted
      | onlyCompleted = filter (csIsComplete . snd)
      | otherwise = id
    ordered = maybeOnlyCompleted $ enumerate rawOrdered

-- ==============================================================================
--  Tree extraction combinators:
--
--  Whenever we add a new state to the chart, we associate with it a
--  subtree-builder, which serves us later (we get_subtrees() is called).
--  These builders combine partial trees to form bigger ones, according to
--  the rules of the grammar
-- ==============================================================================

buildPropagate :: ChartState -> SubtreeFunc
buildPropagate st = SubtreeFunc (Set.toList . getSubtrees st) ("BUILD_PROPAGATE: " ++ strState st)

buildSubstitution :: ChartState -> ChartState -> SubtreeFunc
buildSubstitution st st2 =
  SubtreeFunc f $ unwords ["BUILD_SUBSTITUTION:", strState st, strState st2]
  where
    f chart =
      [ deepSubstitute (csDot st) (NodeTree t2) t1
      | t1 <- Set.toList $ getSubtrees st chart
      , t2 <- Set.toList $ getSubtrees st2 chart
      ]

buildAux :: ChartState -> ChartState -> SubtreeFunc
buildAux st st2 = SubtreeFunc f $ unwords ["BUILD_AUX:", strState st, strState st2]
  where
    f chart =
      [ substituteFoot t1 t2
      | t1 <- Set.toList $ getSubtrees st chart
      , t2 <- Set.toList $ getSubtrees st2 chart
      ]

-- ==============================================================================
--  Parser
-- ==============================================================================
-- | handles the case of left-adjunction rules (2) and (3)
handleLeftAdj :: TIG -> Int -> ChartState -> State Chart ()
handleLeftAdj grammar index st
  | csDot st /= 0 = return ()
  | otherwise = do
    -- (2)
    forM_ (getLeftAuxTreesFor (csTree st ^. treeRoot) grammar) $ \t ->
      chartAdd (ChartState t 0 (csJ st) (csJ st)) ("[2]/" ++ show index) Nothing
    -- (3)
    orderedStates <- State.gets (^. chartOrderedStates)
    forM_ (enumerate orderedStates) $ \(index2, st2) ->
      when
      (  csTree st2 ^. treeType == LeftAux
      && csTree st ^. treeRoot == csTree st2 ^. treeRoot
      && csJ st == csI st2
      && csIsComplete st2
      ) $
      chartAdd (ChartState (csTree st) 0 (csI st) (csJ st2))
      ("[3]/" ++ show index ++ "," ++ show index2) (Just (buildAux st st2))

type Token = String

-- | handles the case of scanning rules (4), (5) and (6)
handleScan :: TIG -> Int -> ChartState -> Maybe Token -> State Chart ()
handleScan _grammar index st token =
  case nextProduction st of
  Just (NodeTerminal str)
    | Just str == token ->
      -- (4)
      chartAdd
      (ChartState (csTree st) (csDot st+1) (csI st) (csJ st+1))
      ("[4]/" ++ show index) (Just (buildPropagate st))
    | str == "" ->
      -- (5)
      chartAdd
      (ChartState (csTree st) (csDot st+1) (csI st) (csJ st))
      ("[5]/" ++ show index) (Just (buildPropagate st))
  Just (NodeFoot _) ->
    -- (6)
    chartAdd
    (ChartState (csTree st) (csDot st+1) (csI st) (csJ st))
    ("[6]/" ++ show index) (Just (buildPropagate st))
  _ -> return ()

-- | handles the case of substitution rules (7) and (8)
handleSubstitution :: TIG -> Int -> ChartState -> State Chart ()
handleSubstitution grammar index st =
  case nextProduction st of
  Just (NodeNonTerminal prod) -> do
    -- (7)
    forM_ (getInitTreesFor prod grammar) $ \t ->
      chartAdd (ChartState t 0 (csJ st) (csJ st))
      ("[7]/" ++ show index) Nothing
    -- (8)
    orderedStates <- State.gets (^. chartOrderedStates)
    forM_ (enumerate orderedStates) $ \(index2, st2) ->
      when
      (  csTree st2 ^. treeRoot == prod
      && csJ st == csI st2
      && csIsComplete st2
      && csTree st2 ^. treeType == InitTree
      ) $
      chartAdd (ChartState (csTree st) (csDot st+1) (csI st) (csJ st2))
      ("[8]/" ++ show index ++ "," ++ show index2) (Just (buildSubstitution st st2))
  _ -> return ()

-- | handles the case of subtree-traversal rules (9) and (10)
handleSubtreeTraversal :: TIG -> Int -> ChartState -> State Chart ()
handleSubtreeTraversal _grammar index st =
  case nextProduction st of
  Just (NodeTree x) -> do
    -- (9)
    chartAdd (ChartState x 0 (csJ st) (csJ st))
      ("[9]/" ++ show index) Nothing

    -- (10)
    orderedStates <- State.gets (^. chartOrderedStates)
    forM_ (enumerate orderedStates) $ \(index2, st2) ->
      when
      ( csTree st2 == x
      && csJ st == csI st2
      && csIsComplete st2
      ) $
      chartAdd (ChartState (csTree st) (csDot st + 1) (csI st) (csJ st2))
      ("[10]/" ++ show index ++ "," ++ show index2)
      (Just (buildSubstitution st st2))
  _ -> return ()

-- | handles the case of right-adjunction rules (11) and (12)
handleRightAdj :: TIG -> Int -> ChartState -> State Chart ()
handleRightAdj grammar index st
  | not (csIsComplete st) = return ()
  | otherwise = do
    -- (11)
    forM_ (getRightAuxTreesFor (csTree st ^. treeRoot) grammar) $ \t ->
      chartAdd (ChartState t 0 (csJ st) (csJ st))
      ("[11]/" ++ show index) Nothing
    -- (12)
    orderedStates <- State.gets (^. chartOrderedStates)
    forM_ (enumerate orderedStates) $ \(index2, st2) ->
      when
      (  csTree st2 ^. treeType == RightAux
      && csTree st2 ^. treeRoot == csTree st ^. treeRoot
      && csJ st == csI st2
      && csIsComplete st2
      ) $
      chartAdd
      (ChartState (csTree st) (length (csTree st ^. treeChildren))
       (csI st) (csJ st2))
      ("[12]/" ++ show index ++ "," ++ show index2) (Just (buildAux st st2))

parseChart :: TIG -> NonTerminal -> [String] -> Chart
parseChart grammar startSymbol tokens = (`execState` emptyChart) $ do
  -- (1)
  forM_ (getInitTreesFor startSymbol grammar) $ \t ->
    chartAdd (ChartState t 0 0 0) "[1]" Nothing
  mainLoop
  where
    paddedTokens = Nothing : map Just tokens
    -- run (2)-(12) until no more changes occur
    mainLoop = do
      orderedStates <- State.gets (^. chartOrderedStates)
      forM_ (enumerate orderedStates) $ \(index, st) -> do
        handleLeftAdj grammar index st
        let tok = join $ paddedTokens ^? ix (csJ st+1)
        handleScan grammar index st tok
        handleSubstitution grammar index st
        handleSubtreeTraversal grammar index st
        handleRightAdj grammar index st
      changed <- state' commit
      when changed mainLoop

-- | The actual parser: it takes a TIG grammar object, a start symbol
-- (NonTerminal) of that grammar, and a list of tokens, and returns
-- (hopefully) all possible parse trees for them.
--
-- It works by first applying the initialization rule (1),
-- then applying rules (2)-(12) for as long as the chart keeps changing,
-- and once it's stable, it looks for matching states according to
-- acceptance rule (13).
--
-- It then takes all matching states (normally there should be only one),
-- extracts the trees of each state, and returns a set of them.
--
-- Note that TIG is assumed to be lexicalized, or at least finitely-ambiguous,
-- so we know the number of trees is bounded.
--
-- The parsing is done in O(|G|^2 * n^3), as discussed in the paper,
-- and tree extraction is performed in amortized linear time, per each tree.
parse :: TIG -> NonTerminal -> [Token] -> Set Tree
parse grammar startSymbol tokens =
  case matches of
  [] -> E.throw $ ParsingError "Grammar does not derive the given sequence"
  _ -> assert (AssertionError "make sure we didn't lose all trees, for then it's our fault")
       (not . Set.null) trees
  where
    finalChart =
      parseChart grammar startSymbol tokens
    trees =
      -- extract trees, drop ones that do not generate the correct token sequence:
      Set.fromList
      [ t
      | (_, m) <- matches
      , t <- Set.toList $ getSubtrees m finalChart
      , mapM (^? _NodeTerminal) (treeLeaves t) == Just tokens
      ]
    -- (13)
    matches =
      [ (index, st)
      | (index, st) <- enumerate $ finalChart ^. chartOrderedStates
      , csIsComplete st
      , csI st == 0
      , csJ st == length tokens
      , csTree st ^. treeRoot == startSymbol
      , csTree st ^. treeType == InitTree
      ]
