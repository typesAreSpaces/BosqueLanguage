constant a : Type
universe u

inductive vector (a : Type u) : nat -> Type u
| nil {} : vector 0
| cons : Π {n} , a -> vector n -> vector (n + 1)

namespace vector

local notation h :: t := cons h t

def tail_aux {α : Type} {n m : ℕ} (v : vector α m) :
    m = n + 1 → vector α n :=
vector.cases_on v
  (assume H : 0 = n + 1, nat.no_confusion H)
  (assume m (a : α) w : vector α m,
    assume H : m + 1 = n + 1,
      nat.no_confusion H (λ H1 : m = n, eq.rec_on H1 w))

def tail {α : Type} {n : ℕ} (v : vector α (n+1)) :
  vector α n :=
tail_aux v rfl

#check tail 

end vector
