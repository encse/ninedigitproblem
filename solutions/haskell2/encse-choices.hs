import Control.Monad.List

fromDigits = foldr shift 0
    where shift d s = 10 * s + d

p `divides` q = q `mod` p == 0

choices :: [a] -> [(a, [a])]
choices  []      = []
choices  (x:xs)  = (x,xs):(map extend $ choices xs)
    where extend (y, ys) = (y, x:ys)

ninedigits = map fromDigits $ iter [1..9] 0 []
    where  iter []  _  ds = return ds
           iter cs  n  ds = do (d, cs') <- choices cs
                               let ds' = d:ds
                                   n' = n + 1
                               guard $ n' `divides` fromDigits ds'
                               iter cs' n' ds'
