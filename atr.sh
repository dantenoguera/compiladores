echo "
  ┌────┐
  │    │
  │++++│  X
 ┌┤++++│  │
 ││++++│  │
 ││++++│  │
 └┤++++│  │
  │    │ 
  └────┘
" | lolcat -F 0.5


for p in progs/*; do
    stack run -- -l $p
done
