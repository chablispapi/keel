{-# LANGUAGE BangPatterns #-}
module Main where

import Control.Exception (evaluate)
import Data.Array.IO (IOUArray, newArray_, readArray, writeArray)
import Data.Bits
import Data.Int
import Data.Word
import System.Environment (getArgs)

data List = Nil | Cons !Int !List
data Tree = Leaf !Int32 | Node !Int32 !Tree !Tree
data Bin = Tip | Branch !Bin !Bin

loop, churn :: Int -> Int -> Int
loop !i !a = if i < 1 then a else loop (i-1) (a+i)
churn !i !a = if i < 1 then a else let (!p,!q) = (i,a) in churn (p-1) (q+1)
fib :: Int -> Int
fib n = if n < 2 then n else fib (n-1) + fib (n-2)
range :: Int -> List -> List
range !n !a = if n < 1 then a else range (n-1) (Cons n a)
mapList :: List -> List
mapList Nil = Nil
mapList (Cons x xs) = Cons (x+1) (mapList xs)
repeatMap :: Int -> List -> List
repeatMap !n !xs = if n < 1 then xs else repeatMap (n-1) (mapList xs)
sumList :: List -> Int
sumList Nil = 0
sumList (Cons x xs) = x + sumList xs
insert :: (Int -> Int -> Bool) -> Int -> List -> List
insert _ x Nil = Cons x Nil
insert lt x xs@(Cons y ys) = if lt x y then Cons x xs else Cons y (insert lt x ys)
sortList :: (Int -> Int -> Bool) -> List -> List
sortList _ Nil = Nil
sortList lt (Cons x xs) = insert lt x (sortList lt xs)

next :: Word64 -> Word64
next x = let a = x `xor` (x `shiftL` 13); b = a `xor` (a `shiftR` 7)
         in b `xor` (b `shiftL` 17)
value :: Word64 -> Int32
value x = fromIntegral (x `rem` 1000)
build :: Int -> Word64 -> Tree
build 0 s = Leaf (value s)
build d s = Node (value s) (build (d-1) (next s)) (build (d-1) (next (s+1)))
sumTree :: Tree -> Int -> Int
sumTree (Leaf v) p = fromIntegral v `xor` p
sumTree (Node v l r) p = (fromIntegral v `xor` p) + sumTree l p + sumTree r p
make :: Int -> Bin
make 0 = Tip
make d = Branch (make (d-1)) (make (d-1))
check :: Bin -> Int
check Tip = 1
check (Branch l r) = 1 + check l + check r
-- Keep repeated construction inside IO so GHC cannot hoist one pure tree/check
-- out of the iteration loop. Disabling CSE also preserves two distinct children.
{-# NOINLINE treeCheck #-}
treeCheck :: Int -> IO Int
treeCheck d = evaluate (check (make d))
bintrees :: Int -> IO ()
bintrees n = do
  treeCheck (n+1) >>= print
  long <- evaluate (make n)
  let sums !d !i !a = if i == 0 then pure a else do
        x <- treeCheck d
        sums d (i-1) (a+x)
  mapM_ (\d -> do
    let iters = (1 :: Int) `shiftL` (n-d+4)
    print iters
    print d
    sums d iters 0 >>= print) [4,6..n]
  print (check long)
arraySum :: Int -> IO ()
arraySum n = do
  xs <- newArray_ (0,n-1) :: IO (IOUArray Int Int32)
  let fill !i !r = if i == n then pure () else do
        let r2 = next r
        writeArray xs i (value r2)
        fill (i+1) r2
      scan !p !i !a = if i == n then pure a else do
        x <- readArray xs i
        scan p (i+1) (a + (fromIntegral x `xor` p))
      passes !p !a = if p == 8 then pure a else scan p 0 a >>= passes (p+1)
  fill 0 12345
  print n
  passes (0 :: Int) (0 :: Int) >>= print
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["loop",n] -> print (loop (read n) 0)
    ["churn",n] -> print (churn (read n) 0)
    ["fib",n] -> print (fib (read n))
    ["map",n] -> print (sumList (repeatMap (read n) (range 1000 Nil)))
    ["sort",n] -> print (sumList (sortList (<) (sortList (>) (range (read n) Nil))))
    ["sum",n] -> arraySum (read n)
    ["tree",n] -> do
      let d = read n; t = build d 12345
      print ((1 `shiftL` (d+1))-1 :: Int)
      print (sum [sumTree t p | p <- [0..7]])
    ["bintrees",n] -> bintrees (read n)
    _ -> error "usage: bench NAME N"
