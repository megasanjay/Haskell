-- Lab 6: Convert regular expressions to FSMs

import Data.List (nub, sort)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Control.Monad (replicateM)


---------------- Some helper functions for lists and sets -------------------

-- Normalize a list, i.e., sort and remove (now adjacent) duplicates.
-- Two lists determine the same set if they normalize to the same list
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- Cartesian product of two lists (preserves order)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerlist of a list (preserves order)
powerlist :: [a] -> [[a]]
powerlist xs = [] : ne_powerlist xs where
  ne_powerlist [] = []
  ne_powerlist (x:xs) = let ys = ne_powerlist xs in [x] : map (x:) ys ++ ys



---------------- Regular expressions and finite state machines --------------

-- Fixed alphabet, but everything below should work for any sigma!
sigma = "ab"


-- Regular expressions
data RE = Empty | Letter Char | Plus RE RE | Cat RE RE | Star RE

instance (Show RE) where    -- use precedence to minimize parentheses
  showsPrec d Empty        = showString "@"
  showsPrec d (Letter c)   = showString [c]
  showsPrec d (Plus r1 r2) = showParen (d > 6) $  -- prec(Plus) = 6
                             showsPrec 6 r1 .
                             showString "+" .
                             showsPrec 6 r2
  showsPrec d (Cat r1 r2)  = showParen (d > 7) $  -- prec(Cat) = 7
                             showsPrec 7 r1 .
                             showsPrec 7 r2
  showsPrec d (Star r1)    = showsPrec 9 r1 .     -- prec(Star) = 8
                             showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RE
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Plus r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)


-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'


---------------- Functions from Lab 4, ported to FSM a ------------------------

-- Note: All functions below assume that the machine is correct

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

-- Two definitions of acceptance of a string by an FSM
delta_1 :: Eq a => FSM a -> a -> Char -> a
delta_1 = ap . delta

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta_1

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m w = elem (delta_star m (start m) w) (finals m)

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m q [] = elem q (finals m)
accept2_aux m q (a:w) = accept2_aux m (delta_1 m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m w = accept2_aux m (start m) w


-- even_as is a machine that accepts strings with an even number of a's
-- states: (number of a's read so far) mod 2
even_as :: FSM Int
even_as = FSM {
  states = [0,1],
  start  = 0,
  finals = [0],
  delta  = [(i, a, d i a) | i <- [0,1], a <- sigma]
  } where d i 'a' = (i + 1) `mod` 2
          d i c   = i

-- no_aaa is a machine that accepts strings that don't have three a's in a row
-- states: number of a's in a row just read (n = 0, 1, 2), 3 is a trap
no_aaa :: FSM Int
no_aaa = FSM {
  states = [0,1,2,3],
  start  = 0,
  finals = [0,1,2],
  delta  = [(i, a, d i a) | i <- [0..3], a <- sigma]
  } where d i 'a' = min 3 (i+1)
          d 3 c   = 3
          d i c   = 0


-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = FSM {
  states = [0],
  start  = 0,
  finals = [],
  delta  = [(0, a, 0) | a <- sigma]
  }


-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM x = FSM {
  states = [0,1,2],
  start  = 0,
  finals = [1],
  delta  = [(i, a, d i a) | i <- [0..2], a <- sigma]
  } where d i c = if i == 0 && c == x then 1 else 2


-- Machine that accepts the language {w} where w in sigma*
stringFSM :: [Char] -> FSM Int
stringFSM w = FSM {
  states = [0..n+1],
  start  = 0,
  finals = [n],
  delta  = [(i, a, d i a) | i <- [0..n+1], a <- sigma]
  } where n = length w
          d i a = if i >= n || w !! i /= a then n+1 else i+1


-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM m1 m2 = FSM {
  states = qs,
  start  = (start m1, start m2),
  finals = [q | q <- qs, elem (fst q) (finals m1) || elem (snd q) (finals m2)],
  delta  = [(q, a, d q a) | q <- qs, a <- sigma]
  } where
    qs = states m1 >< states m2
    d (q1,q2) a = (ap (delta m1) q1 a, ap (delta m2) q2 a)


-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM m1 m2 = FSM {
  states = qs,
  start  = (s1, [s2 | elem s1 fs1]),
  finals = [q | q <- qs, overlap (snd q) (finals m2)],
  delta  = [(q, a, d q a) | q <- qs, a <- sigma]
  } where
    qs  = states m1 >< powerlist (states m2)
    s1  = start m1
    s2  = start m2
    fs1 = finals m1
    d (q1,b) a = (q1', b') where
      q1' = ap (delta m1) q1 a
      b'  = norm $ [s2 | elem q1' fs1] ++ map (\q2 -> ap (delta m2) q2 a) b


-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM m = FSM {
  states = qs,
  start  = [],
  finals = [b | b <- qs, null b || overlap b fs],
  delta  = [(q, a, d q a) | q <- qs, a <- sigma]
  } where
    qs  = powerlist (states m)
    s  = start m
    fs = finals m
    dm  = delta m
    d [] a = norm $ [s | elem q fs] ++ [q] where q = ap dm s a
    d b a  = norm $ [s | overlap b' fs] ++ b' where
      b' = map (\q -> ap dm q a) b


-- reachable m == the part of m that is reachable from the start state;
-- in addition, converts states to Int's
reachable :: Ord a => FSM a -> FSM Int
reachable m = FSM {
  states = qs,
  start  = Set.findIndex s qset,
  finals = [q | q <- qs, elem (Set.elemAt q qset) (finals m)],
  delta  = [(q, a, d q a) | q <- qs, a <- sigma]
  } where
    s = start m
    dm = delta m
    qs = [0..n-1]
    n = Set.size qset
    qset = stable $ iterate close (Set.fromList [s], Set.empty)
    stable ((fr,xs):rest) = if Set.null fr then xs else stable rest
    close (fr, xs) = (fr', xs') where
      xs' = Set.union fr xs
      fr' = Set.unions $ map (\a -> Set.map (\q -> ap dm q a) fr \\ xs') sigma
    d q a = Set.findIndex (ap dm (Set.elemAt q qset) a) qset


-- Converts a regular expression to a FSM on states [0..n]
re2fsm :: RE -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Letter c) = letterFSM c
re2fsm (Plus r1 r2) = reachable $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reachable $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r) = reachable $ starFSM (re2fsm r)


-- All strings over sigma of length 10 or less
strings = concat $ [replicateM i sigma | i <- [0..10]]



---- Lab 6 begins here ------------------------------------------------------

-- Exercise 1: (abb+b)*

ex1  = toRE "ab.b.b+*"
m1   = re2fsm ex1   -- 23 states, 9 finals
fsm1 = FSM {        -- 4 states, 1 final
  states = [0..3],
  start  = 0,
  finals = [0],
  delta  = [(0, 'a', 1), (0, 'b', 0),
            (1, 'a', 3), (1, 'b', 2),
            (2, 'a', 3), (2, 'b', 0),
            (3, 'a', 3), (3, 'b', 3)]
  }
test1 = all (\w -> accept1 m1 w == accept1 fsm1 w) strings


-- Replace this comment with Exercises 2-7, as above

--Exercise 2: ( ( (aa)* + (aba)* + (baa)* + (baba*) + (abab)* ) b* )*
--Exercise 2: b*(ab*ab*)*
ex2 = toRE "b*ab*.ab*..*."
m2  = re2fsm ex2
fsm2 = FSM {
  states = [0..2],
  start  = 0,
  finals = [0, 2],
  delta  = [(0, 'a', 1), (0, 'b', 0),
            (1, 'a', 2), (1, 'b', 1),
            (2, 'a', 1), (2, 'b', 1)]
  }
test2 = all (\w -> accept1 m2 w == accept1 fsm2 w) strings

--Exercise 3: (aa*b*b + ba*b*a)*
ex3 = toRE "aa*.b*.b.ba*.b*.a.+*"
m3  = re2fsm ex3
fsm3 = FSM {
  states = [0..3],
  start = 0,
  finals = [3],
  delta = [(0, 'a', 1), (0, 'b', 2), 
           (1, 'a', 1), (1, 'b', 3), 
		   (2, 'b', 2), (2, 'a', 3),
		   (3, 'a', 3), (3, 'b', 3)]
  }

test3 = all (\w ->accept1 m3 w == accept2 fsm3 w) strings
---- Recursive definitions of predicates on RE

-- is_letter c r == True iff the language accepted by r is exactly the letter c
-- i.e., iff [[r]] = [[c]]
is_letter :: Char -> RE -> Bool
is_letter = undefined

-- uses_only cs r == True iff all strings matching r use only the letters in cs
-- i.e., iff [[r]] subset cs*
uses_only :: [Char] -> RE -> Bool
uses_only  = undefined
