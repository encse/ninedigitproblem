import Control.Monad.List

fromDigits = foldr shift 0
    where shift d s = 10 * s + d

p `divides` q = q `mod` p == 0

encse = map fromDigits $ encse' 0 []
    where encse' 9 ds = return ds
          encse' n ds = do d <- [1..9]
                           let ds' = d:ds
                               n' = n + 1
                           guard $ not (d `elem` ds)
                           guard $ n' `divides` fromDigits ds'
                           encse' n' ds'
