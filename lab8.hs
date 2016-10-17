-- Lab 8 (String matching with regular expressions)

import Control.Applicative
import Control.Monad (replicateM)

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


---------------- Lab 8 starts here ----------------

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = [(take x xs, drop x xs) | x <- [0..(length xs)]]


-- Algorithm 1, using splits
match1 :: RE -> [Char] -> Bool
match1 Empty w = False
match1 (Letter c) w = 
match1 (Union r1 r2) w = undefined
match1 (Cat r1 r2) w = undefined
match1 (Star r) w = undefined


-- Algorithm 2, using continuations
match2 :: RE -> [Char] -> Bool
match2 r w = matchc r w null where
  -- matchc r w k == True iff w = w1*w2, r matches w1, and k w2 == True
  matchc :: RE -> [Char] -> ([Char] -> Bool) -> Bool
  matchc Empty w k = undefined
  matchc (Letter c) ws k = undefined
  matchc (Union r1 r2) w k = undefined
  matchc (Cat r1 r2) w k = undefined
  matchc r@(Star r1) w k = undefined



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
--time1 = do
  --putStrLn "Starting"
  --time1' $ Time'' `seq`


-- Timing experiments between the winner of match1 and match2 vs acceptance
-- by the associated FSM
