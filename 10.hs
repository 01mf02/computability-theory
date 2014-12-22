h 0 x = x + 1
h n x = iterate (h $ n - 1) x !! x
