module Data.Bits.Size where

-- | Number of bits needed to encode the given
-- non-negative integer
usedBits :: (Integral a, Num b) => a -> b
usedBits = (+ 1) . log2
  where
    log2 :: (Integral a, Num b) => a -> b
    log2 x
      | x < 0 = error "Argument to log2 must be non-negative"
      | otherwise = log2' x
      where
        log2' 0 = 0
        log2' 1 = 0
        log2' y = 1 + (log2' $ quot y 2)
