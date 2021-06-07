
{--

f(r) = 11^r mod 15

g :: B^2 x B^4 ⟷ B^2 x B^4
g(r,h) = (r , h ⊕ f(r))

g(r,h) where r even and h even = (r , h+1)
g(r,h) where r even and h odd = (r , h-1)
g(r,0) where r odd = (r,11)
g(r,1) where r odd = (r,10)
g(r,2) where r odd = (r,9)
g(r,3) where r odd = (r,8)
g(r,4) where r odd = (r,15)
g(r,5) where r odd = (r,14)
g(r,6) where r odd = (r,13)
g(r,7) where r odd = (r,12)
g(r,8) where r odd = (r,3)
g(r,9) where r odd = (r,2)
g(r,10) where r odd = (r,1)
g(r,11) where r odd = (r,0)
g(r,12) where r odd = (r,7)
g(r,13) where r odd = (r,6)
g(r,14) where r odd = (r,5)
g(r,15) where r odd = (r,4)

0000 => 1011
0001 => 1010
0010 => 1001
0011 => 1000
0100 => 1111
0101 => 1110
0110 => 1101
0111 => 1100
1000 => 0011
1001 => 0010
1010 => 0001
1011 => 0000
1100 => 0111
1101 => 0110
1110 => 0101
1111 => 0100


--}
