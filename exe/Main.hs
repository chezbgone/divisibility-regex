{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Control.Monad (forM_)
import Data.Either (rights)

data Bit = Zero | One
  deriving (Eq)

instance Show Bit where
  show Zero = "0"
  show One  = "1"

-- invariants:
-- * start in nodes, end in nodes
-- * for each (a, b) in (keys edges), a in nodes and b in nodes
data DFA v e = DFA
  { nodes :: [v]
  , start :: v
  , end   :: v
  , edges :: Map (v, v) e
  }

data Regex a
  = Null
  | Epsilon
  | Atom a
  | Seq (Regex a) (Regex a)
  | Union (Regex a) (Regex a)
  | Star (Regex a)
  deriving (Eq)

instance Show a => Show (Regex a) where
  showsPrec :: Show a => Int -> Regex a -> ShowS
  showsPrec p r =
    case r of
      Null      -> showString "∅"
      Epsilon   -> showString "ε"
      Atom a    -> showString $ show a
      Seq s t   -> showParen (p > 7) $ showsPrec 7 s . showString " " . showsPrec 7 t
      Union s t -> showParen (p > 6) $ showsPrec 6 s . showString " ∪ " . showsPrec 6 t
      Star s    -> showParen (p > 8) $ showsPrec 8 s . showString "*"

instance Eq a => Num (Regex a) where
  r + s = simplifyRegex $ Union r s
  r * s = simplifyRegex $ Seq r s
  abs = undefined
  signum = undefined
  fromInteger = undefined
  negate = undefined

--------------------------
-- general DFA/regex stuff

simplifyRegex :: Eq a => Regex a -> Regex a
simplifyRegex r =
  case r of
    Seq Null _    -> Null
    Seq _ Null    -> Null
    Seq Epsilon a -> simplifyRegex a
    Seq a Epsilon -> simplifyRegex a
    Seq a b       -> Seq (simplifyRegex a) (simplifyRegex b)
    Union Null a  -> simplifyRegex a
    Union a Null  -> simplifyRegex a
    Union a b     -> Union (simplifyRegex a) (simplifyRegex b)
    Star Null     -> Epsilon
    Star Epsilon  -> Epsilon
    _             -> r

data ExtraNode = Start | End
  deriving (Eq, Ord, Show)

augmentDFA :: (Ord v) => DFA v (Regex a) -> DFA (Either ExtraNode v) (Regex a)
augmentDFA dfa = DFA
  { nodes = fmap pure nodes <> [new_start, new_end]
  , start = new_start
  , end = new_end
  , edges =
    M.mapKeys inject edges
      `M.union`
    M.fromList
      [ ((new_start, pure start), Epsilon)
      , ((pure end, new_end), Epsilon)
      , ((new_start, new_end), Epsilon)
      ]
  }
  where
    DFA {..} = dfa
    inject (a, b) = (pure a, pure b)
    new_start = Left Start
    new_end = Left End

-- requires `length nodes > 2`
condense :: (Eq a, Ord u) => DFA u (Regex a) -> DFA u (Regex a)
condense dfa = DFA
  { nodes = rest
  , start = start
  , end = end
  , edges = new_edges
  }
  where
    DFA {..} = dfa
    v = head nodes
    rest = tail nodes
    transition x y = M.findWithDefault Null (x, y) edges
    new_edges = M.fromList
      [ ((a, b), result)
      | let vv = transition v v
      , a <- rest
      , b <- rest
      , let ab = transition a b
      , let av = transition a v
      , let vb = transition v b
      , let result = av * Star vv * vb + ab
      , result /= Null
      ]

dfaToRegex :: forall a v. (Eq a, Ord v) => DFA v (Regex a) -> Regex a
dfaToRegex dfa = dfaToRegex' (augmentDFA dfa)
  where
    dfaToRegex' :: DFA (Either ExtraNode v) (Regex a) -> Regex a
    dfaToRegex' dfa'
      | length nodes == 2 =
        case edges of
          [((Left Start, Left End), r)] -> r
          _ -> error "invariant error: there should only be one edge left"
      | length nodes > 2 = dfaToRegex' $ condense dfa'
      | otherwise = error "invariant error: there should be at least two nodes"
      where DFA {..} = dfa'

------------------------
-- problem specific code

divisibilityDFA :: Int -> DFA Int (Regex Bit)
divisibilityDFA n = DFA
  { nodes = residues
  , start = 0
  , end = 0
  , edges = edges
  }
  where
    residues = [0 .. (n-1)]
    edges = M.fromList $ do
      k <- residues
      [ ((k, (2 * k)     `mod` n), Atom Zero) ,
        ((k, (2 * k + 1) `mod` n), Atom One ) ]

divisibilityDFA' :: Int -> Int -> DFA Int (Regex Int)
divisibilityDFA' base n = DFA
  { nodes = residues
  , start = 0
  , end = 0
  , edges = edges
  }
  where
    residues = [0 .. (n-1)]
    edges = M.fromListWith Union $ do
      k <- residues
      [ ((k, (base * k + i) `mod` n), Atom i) | i <- [0 .. (base - 1)] ]

divisibilityRegex :: Int -> Regex Bit
divisibilityRegex = dfaToRegex . divisibilityDFA

main :: IO ()
main = do
  let
    showEdge ((Left  u, Left  v), r) = show (u, v) <> "   " <> show r
    showEdge ((Left  u, Right v), r) = show (u, v) <> "   " <> show r
    showEdge ((Right u, Left  v), r) = show (u, v) <> "   " <> show r
    showEdge ((Right u, Right v), r) = show (u, v) <> "   " <> show r

    printNodes state = print $ rights $ nodes state
    printEdges state = forM_ (M.assocs (edges state)) $ putStrLn . showEdge

  let n = 3
  let dfa = augmentDFA $ divisibilityDFA n
  forM_ (take (n+1) (iterate condense dfa)) $ \state -> do
    putStrLn ""
    printNodes state
    printEdges state
