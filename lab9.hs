-- Lab 9: REG closure under other operations
import Data.List (nub, sort)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Control.Monad (replicateM)

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

--DELETE
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

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

-- Bypassability (p.12): byp r == True iff "" in [[r]]
byp :: RE -> Bool
byp Empty = False
byp (Letter c) = False
byp (Union r1 r2) = byp r1 || byp r2
byp (Cat r1 r2) = byp r1 && byp r2
byp (Star r) = True


-- Implement each of the following operations on regular expressions or FSMs

-- [[reverseRE r]] = rev([[r]]), defined by recursion on r
reverseRE :: RE -> RE
reverseRE Empty = Empty
reverseRE (Letter c) = (Letter c)
reverseRE (Union r1 r2) = Union (reverseRE r1) (reverseRE r2)
reverseRE (Cat r1 r2) = Cat (reverseRE r2)(reverseRE r1)
reverseRE (Star r) = Star (reverseRE r)

--Test machine DELETE
even_as :: FSM Int
even_as = FSM {
  states = [0,1],
  start  = 0,
  finals = [0],
  delta  = [(i, a, d i a) | i <- [0,1], a <- sigma]
  } where d i 'a' = (i + 1) `mod` 2
          d i c   = i

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


-- L(complementFSM M) = Sigma^* - L(M)
complementFSM :: Ord a => FSM a -> FSM a
complementFSM m = FSM {
                    states = (states m),
                    start = (start m),
                    finals = [x |x <- (states m), (x `elem` (finals m)) == False ],
                    delta = (delta m)
                    }

-- L(intersectFSM m1 m2) = L(m1) intersect L(m2)
intersectFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a,b)
intersectFSM m1 m2 = FSM {
                       states = [(q1, q2) | q1 <- (states m1), q2 <- (states m2)],
                       start = (start m1, start m2),
                       finals = [(f1, f2) | f1 <- (finals m1), f2 <- (finals m2)],
                       delta = [((qm1, qm2), c, (dm1, dm2)) | (qm1, c, dm1)<-(delta m1), (qm2, c', dm2)<- (delta m2), c == c']
                       }
h :: Char -> [Char]
h 'a' = "aa."
h 'b' = "ba.a."

-- [[himage r h]] = h^*([[r]]), defined by recursion on r
himage :: RE -> (Char -> [Char]) -> RE
himage Empty _ = Empty
himage (Letter c) h = toRE (h c)
himage (Union r1 r2) h = Union (himage r1 h) (himage r2 h)
himage (Cat r1 r2) h = Cat (himage r1 h) (himage r2 h)
himage (Star r) h = Star (himage r h)

sigma  = "ab"
-- L(hinvimage m h) = (h^*)^{-1}(L(m))
hinvimage :: Ord a => FSM a -> (Char -> [Char]) -> FSM a
hinvimage m h = FSM {
                  states = states m,
                  start  = start m,
                  finals  = finals m,
                  delta = [(q, a, (delta_star m (start m) [x | x <- (h a), elem x sigma])) | q <- (states m), a <- sigma]
                  }

-- L(rightq m a) = L(m)/{a} = { w | wa in L(m) }
rightq :: Ord a => FSM a -> Char -> FSM a
rightq m a = FSM{
               states = states m,
               start  = start m,
               finals = [delta_star m (start m) [a] | (delta_star m (start m) [a]) `elem` (finals m)],
               --finals = [q |w <- a , (delta_star m (start m) w) elem (finals m)],
               delta = delta m
               }

-- [[leftq r a]] = {a}\[[r]] = { w | aw in [[r]] }, defined by recursion on r
-- CREATE A DIRECT CONVERSION
leftq :: RE -> Char -> RE
leftq = undefined
