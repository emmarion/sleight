let rec f (n:int) (a:int) = if n = 0 then a else g (n-1) a 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18
and[@inline never] g (n:int) a b c d e h i j k l m o p q r s t u v = if n = 0 then a+b+c+d+e+h+i+j+k+l+m+o+p+q+r+s+t+u+v else f (n-1) (a+b+v)
let () = print_int (f 10_000_000 1)
