def add : nat -> nat -> nat 
| 0 m := m
| (n + 1) m := add n m + 1

#reduce add 123 12
