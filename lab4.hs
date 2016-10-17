-- Sanjay Soundarajan - 109146095
-- CSci 119, Fall 2016, Lab 4

import Data.List

sigma = ['a', 'b']

-- Finite State Machine M = (Q, q0, F, d)
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

-- Check whether a finite state machine (qs, q0, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (q0 is in qs)
-- (3) Final states are states (fs is a subset of qs; don't worry about dups)
-- (4) Transition relation is a function from qs and sigma to qs (exactly one
--     output state for each state and letter from sigma)
unique :: [Int] -> Bool
unique rs = (length rs == length (nub (rs)))

start_state :: Int -> [Int] -> Bool
start_state x rs = x `elem` rs

final_state :: [Int] -> [Int] -> Bool
final_state fs qs = and [ elem x qs | x <- fs]

check_trans :: [(Int, Char, Int)] -> [Int] -> Bool
check_trans _ [] = False -- base case
check_trans [] _ = True 
check_trans (t@(s1, c, s2):ts) states = elem s1 states && elem c sigma && elem s2 states && 
                                        and[s2==s2'| (s1,c,s2) <- (t:ts), (s1',c',s2')<-(t:ts), c == c', s1 == s1'] && check_trans ts states

checkFSM :: FSM -> Bool
checkFSM (qs, q0, fs, ts) = (unique qs) && (start_state q0 qs) && (final_state fs qs) && (check_trans ts qs)

-- Gives the transition function of the machine as a function
-- i.e., delta m q a = the state machine m goes to when reading a in state q
delta :: FSM -> Int -> Char -> Int
delta (qs, q0, fs, ts) q a = minimum [ z | (x, y, z) <- ts, q == x, y == a]

-- Gives the delta* function
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q "" = q
delta_star m q (a:w) = delta_star m (delta m q a) w

accept1_final_state :: FSM -> [Int]
accept1_final_state (qs, q0, fs, ts) = fs

accept1_start_state :: FSM -> Int
accept1_start_state (qs, q0, fs, ts) = q0

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m w = (checkFSM m) && ((delta_star m (accept1_start_state m) w) `elem` (accept1_final_state m))


-- Machine acceptance, Definition 2 (via L_q(M))

accept2_aux_final_state :: FSM -> Int -> Bool
accept2_aux_final_state (qs, q0, fs, ts) q = q `elem` fs

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m q "" = True && checkFSM m && (accept2_aux_final_state m q)
accept2_aux m q (a:w) = accept2_aux m (delta m q a) w

accept2_start_state :: FSM -> Int
accept2_start_state (qs, q0, fs, ts) = q0

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m w = accept2_aux m (accept2_start_state m) w


-- Define a machine that accepts exactly the strings with an even number of a's
-- and test it adequately
let even_a = ([0..3], 0, [2], [(0,'a',1),(1,'a',2),(2,'a',1),(2,'b',2),(0,'b',3),(3,'a',1),(1,'b',1)])

-- Define a machine that accepts exactly the strings that do not contain "aaa"
-- as a substring and test it adequately
let no_aaa = ([0..4],0,[1,2],[(0,'a',1),(0,'b',1),(1,'a',2),(1,'b',1),(2,'a',3),(2,'b',1),(3,'a',4),(3,'b',4),(4,'a',4),(4,'b',4)])
