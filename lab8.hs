-- Lab 8 (String matching with regular expressions)

import Control.Applicative
import Control.Monad (replicateM)
import Text.Printf
import Control.Exception
import System.CPUTime
import Data.List (nub, sort)
import Data.Set (Set, (\\))
import qualified Data.Set as Set

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


-- Regular expressions

data RE = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE
instance (Show RE) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RE
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)

time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "Computation time: %0.9f sec\n" (diff :: Double)
    return v

---------------- Lab 8 starts here ----------------

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = [(take x xs, drop x xs) | x <- [0..(length xs)]]


-- Algorithm 1, using splits
match1 :: RE -> [Char] -> Bool
match1 Empty w = False
match1 (Letter c) w = ((length w) == 1)  && (and[x == c| x <- w])
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or [(match1 r1 w1) && (match2 r2 w2) | (w1, w2) <- splits w]
match1 (Star r) w = (w == "") || or [(match1 r w1) && (match1 (Star r) w2) | (w1, w2) <- splits w, w1 /= "", w2 /= w]

-- Algorithm 2, using continuations
match2 :: RE -> [Char] -> Bool
match2 r w = matchc r w null where
  -- matchc r w k == True iff w = w1*w2, r matches w1, and k w2 == True
  matchc :: RE -> [Char] -> ([Char] -> Bool) -> Bool
  matchc Empty w k = True
  matchc (Letter c) w k = (w /= "") && (c == head w) && (k (tail w))
  matchc (Union r1 r2) w k = (matchc r1 w k || matchc r2 w k)
  matchc (Cat r1 r2) w k = matchc r1 w (\w' -> matchc r2 w' k)
  matchc r@(Star r1) w k = k w || (matchc r1 w (\w' -> (w' /= w) && matchc r w' k))



-- Tests, including some timing experiments with match1 vs match2
-- and with matching and FSM acceptance.


-- All strings over "ab" of length 10 or less
strings = concat $ [replicateM i "ab" | i <- [0..10]]

-- Some regular expressions for testing; you can also try your own
ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once

-- Consistency check 1: test each of these regexs against each string using
-- both match1 and match2. This test should be true, but it doesn't mean
-- the implementations are correct, only that they agree with each other!
test = null [(r,w) | r<-[ab,ttla,ena,bb1], w<-strings, match1 r w /= match2 r w]


-- Consistency check 2: test these regexs and strings agains FSM acceptance


-- Timing experiments with match1 vs match2 here. Include the results
-- of your tests in comments. Be careful about Haskell's laziness!

runtest = do
    putStrLn "Starting..."
    time $ test `seq` return ()
    putStrLn "Done."
-- runtest (a.k.a test) took me 59.88 seconds

test1 =  and [match1 r w | r<-[ab,ttla,ena,bb1], w<-strings]
test2 =  and [match2 r w | r<-[ab,ttla,ena,bb1], w<-strings]

runtestmatch1 = do
    putStrLn "Starting..."
    time $ test1 `seq` return ()
    putStrLn "Done."
-- runtestmatch1 (a.k.a test on match1) took me 0.000065000 seconds

runtestmatch2 = do
    putStrLn "Starting..."
    time $ test2 `seq` return ()
    putStrLn "Done."
    -- runtestmatch2 (a.k.a test on match2) took me 0.000044000 seconds

-- Timing experiments between the winner of match1 and match2 vs acceptance
-- by the associated FSM
fsm1 = FSM {
  states = [0..4],
  start  = 0,
  finals = [3],
  delta  = [(0, 'a', 1), (0, 'b', 3),
            (1, 'a', 2), (1, 'b', 4),
            (2, 'a', 0), (2, 'b', 0),
            (3, 'a', 4), (3, 'b', 2),
            (4, 'a', 4), (4, 'b', 4)]
  }

fsm2 = FSM {
  states = [0..18],
  start  = 0,
  finals = [3],
  delta  = [(0,'a',1), (0,'b',10),
            (1,'a',3), (1,'b',12),
            (2,'a',3), (2,'b',12),
            (3,'a',4), (3,'b',13),
            (4,'a',5), (4,'b',14),
            (5,'a',5), (5,'b',14),
            (6,'a',5), (6,'b',14),
            (7,'a',6), (7,'b',15),
            (8,'a',6), (8,'b',15),
            (9,'a',6), (9,'b',15),
            (10,'a',2), (10,'b',11),
            (11,'a',2), (11,'b',11),
            (12,'a',7), (12,'b',16),
            (13,'a',8), (13,'b',17),
            (14,'a',8), (14,'b',17),
            (15,'a',8), (15,'b',17),
            (16,'a',9), (16,'b',18),
            (17,'a',9), (17,'b',18),
            (18,'a',9), (18,'b',18)]
  }

fsm3 = FSM {
  states = [0..2],
  start  = 0,
  finals = [2],
  delta  = [(0, 'a', 1), (0, 'b', 0),
            (1, 'a', 2), (1, 'b', 1),
            (2, 'a', 1), (2, 'b', 2)]
  }

fsm4 = FSM {
  states = [0..30],
  start  = 0,
  finals = [13,14,15,16,17,18,19,22,23,24,25,26,27,28],
  delta  = [(0,'a',1), (0,'b',9),
            (1,'a',2), (1,'b',10),
            (2,'a',2), (2,'b',10),
            (3,'a',3), (3,'b',11),
            (4,'a',3), (4,'b',11),
            (5,'a',3), (5,'b',11),
            (6,'a',3), (6,'b',11),
            (7,'a',4), (7,'b',12),
            (8,'a',4), (8,'b',12),
            (9,'a',7), (9,'b',22),
            (10,'a',5), (10,'b',13),
            (11,'a',6), (11,'b',14),
            (12,'a',8), (12,'b',23),
            (13,'a',15), (13,'b',20),
            (14,'a',15), (14,'b',20),
            (15,'a',17), (15,'b',18),
            (16,'a',16), (16,'b',19),
            (17,'a',17), (17,'b',19),
            (18,'a',16), (18,'b',21),
            (19,'a',16), (19,'b',21),
            (20,'a',20), (20,'b',20),
            (21,'a',21), (21,'b',21),
            (22,'a',24), (22,'b',29),
            (23,'a',24), (23,'b',29),
            (24,'a',26), (24,'b',27),
            (25,'a',25), (25,'b',28),
            (26,'a',26), (26,'b',28),
            (27,'a',25), (27,'b',30),
            (28,'a',25), (28,'b',30),
            (29,'a',29), (29,'b',29),
            (30,'a',30), (30,'b',30)]
  }
test3 = and [(accept1 fsm1 w) && (accept1 fsm2 w) && (accept1 fsm3 w) && (accept1 fsm4 w)| w <- strings]

runtestaccept = do
    putStrLn "Starting..."
    time $ test3 `seq` return ()
    putStrLn "Done."
-- runtestaccept (a.k.a test on accept1 with 4 FSMs) took me 0.000058000 seconds
