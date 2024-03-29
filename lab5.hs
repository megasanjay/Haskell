-- Lab 5: Convert regular expressions to FSMs

{-#LANGUAGE GADTs, StandaloneDeriving #-}   -- required for defn. of RegExp a

import Data.List (nub, sort, subsequences)


-- Fixed alphabet, but everything below should work for any sigma!
sigma = "ab"

-- Regular expressions indexed by the state-type of their associated FSMs
data RegExp a where
  Empty  :: RegExp Int
  Letter :: Char -> RegExp Int
  Plus   :: (Ord a, Ord b) => RegExp a -> RegExp b -> RegExp (a, b)
  Cat    :: (Ord a, Ord b) => RegExp a -> RegExp b -> RegExp (a, [b])
  Star   :: Ord a => RegExp a -> RegExp [a]
deriving instance Show (RegExp a)

-- Finite state machines indexed by the type of their states
-- M = (states, start, final, transitions)  
type FSM a = ([a], a, [a], [(a, Char, a)])


---------------- Solution to Lab 4, ported to FSM a ------------------------
  
-- no_dups xs = "xs has no duplicates"
no_dups :: Eq a => [a] -> Bool
no_dups [] = True           
no_dups (x:xs) = not (elem x xs) && no_dups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys

-- func3 as bs ts == "ts determines a function from (as x bs) to cs"
func3 :: (Eq a, Eq b, Eq c) => [a] -> [b] -> [c] -> [(a,b,c)] -> Bool
func3 as bs cs ts = and [single (thirds a b ts) cs | a <- as, b <- bs] where
  thirds a b ts = [c' | (a',b',c') <- ts, a' == a, b' == b]
  single [x] ys = elem x ys
  single _ _ = False

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = no_dups qs &&        -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func3 qs sigma qs d  -- (4)
                           
-- All functions below assume that the machine is correct

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

delta :: Eq a => FSM a -> a -> Char -> a
delta (_, _, _, d) = ap d
                                             
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(qs, q0, fs, d) w = elem (delta_star m q0 w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m q (a:w) = accept2_aux m (delta m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, q0, _, _) w = accept2_aux m q0 w

-- even_as is a machine that accepts strings with an even number of a's
-- states: (number of a's read so far) mod 2
even_as :: FSM Int
even_as = ([0,1], 0, [0], [(i, a, d i a) | i <- [0,1], a <- sigma]) where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

-- no_aaa is a machine that accepts strings that don't have three a's in a row
-- states: number of a's in a row just read (n = 0, 1, 2), 3 is a trap
no_aaa :: FSM Int
no_aaa = ([0..3], 0, [0..2], [(i, a, d i a) | i <- [0..3], a <- sigma]) where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0


---------------- Some additional useful functions --------------------------

-- Normalize a list, i.e., sort and remove (now adjacent) duplicates.
-- Two lists determine the same set if they normalize to the same list
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]   

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 4 begins here -----------------------------------------

powerlist :: [a] -> [[a]]
powerlist xs = [] : ne_powerlist xs where
  ne_powerlist [] = []
  ne_powerlist (x:xs) = let ys = ne_powerlist xs in [x] : map (x:) ys ++ ys

-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], [(0,a,0) | a <- sigma])

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM x = ([0..2], 0, [1], [(i, a, d i a) | i <- [0..2], a <- sigma]) where
                  d 0 x = 1
                  d _ _ = 2

-- Machine that accepts the language {w} where w in sigma*
stringFSM :: [Char] -> FSM Int
stringFSM w = ([0..n+1], 0, [n], [(i, a, d i a) | i <- [0..n+1], a <- sigma]) where
                  n = length w
                  d i a = if i >= n || w !! i /= a then n+1 else i+1

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1,q2) | q1 <- qs1, q1 `elem` fs1, q2 <- qs2, q2 `elem` fs2]
--fs = [q | q <- qs, (fst q) `elem` fs1 || (snd q) `elem` fs2]
  d  = [(q, a, step q a) | q <- qs, a <- sigma]
  step (q1, q2) a = (ap d1 q1 a, ap d2 q2 a)

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< powerlist qs2
--qs = [(q1, b) | q1 <- qs1, b <- powerlist qs2, q1 `notElem` fs1 || s2 `elem` b]  
  s  = (s1, [s2 | s1 `elem` fs1])
--s  = (s1, if s1 `elem` fs1 then [s2] else [])
  fs = [q | q <- qs, overlap (snd q) fs2]
  d  = [(q, a, step q a) | q <- qs, a <- sigma]
  step (q1, b) a = (q1', b') where
    q1' = ap d1 q1 a
    b' = norm $ [s2 | q1' `elem` fs1] ++ map (\q2 -> ap d2 q2 a) b

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = powerlist qs1
--qs = [b | b <- powerlist qs1, not (overlap b fs1) || s1 `elem` b]  
  s  = []
  fs = [b | b <- qs, null b || overlap b fs1]
  d  = [(q, a, step q a) | q <- qs, a <- sigma]
  step [] a = norm $ [s1 | q `elem` fs1] ++ [q] where q = ap d1 s1 a
  step b a = norm $ [s1 | overlap b' fs1] ++ b' where
    b' = map (\q -> ap d1 q a) b


-- Convert a regular expression to a finite state machine
reg2fsm :: RegExp a -> FSM a
reg2fsm Empty = emptyFSM
reg2fsm (Letter c) = letterFSM c
reg2fsm (Plus r1 r2) = unionFSM (reg2fsm r1) (reg2fsm r2)
reg2fsm (Cat r1 r2) = catFSM (reg2fsm r1) (reg2fsm r2)
reg2fsm (Star r) = starFSM (reg2fsm r)



-- Bonus Feature (for testing):

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, q0, fs, d) = (qs', q0, fs', d') where
  qs' = sort $ stable $ iterate close ([q0], [])
  fs' = filter (`elem` qs') fs
  d'  = filter (\(q,_,_) -> q `elem` qs') d
  stable ((fr,qs):rest) = if null fr then qs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = nub $ filter (`notElem` xs') (concatMap step fr)
    step q = map (ap d q) sigma
