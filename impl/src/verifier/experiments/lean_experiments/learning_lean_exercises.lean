namespace final_exercise

lemma double_neg : Π (p : Prop), p -> ¬¬ p := 
    fun p : Prop, 
    fun hp : p, 
    fun hp2 : ¬ p, 
    hp2 hp

lemma swap_neg : Π (p : Prop), (¬ p -> p) -> (¬ p -> ¬ ¬ p) := 
    fun p : Prop, 
    fun hp1 : (¬ p -> p), 
    fun hp2 : ¬ p, 
    double_neg p (hp1 hp2)

theorem final_exercise : Π (p : Prop), ¬ (p <-> ¬p) := 
assume p : Prop,
assume h1 : (p <-> ¬ p), 
let part1 := 
    fun hp : p, 
    show false, from
    absurd (iff.elim_left h1 hp) (double_neg p hp) in
let part2 := 
    fun hp : ¬p, 
    show false, from 
    absurd hp (swap_neg p (iff.elim_right h1) hp) in
show false, from 
absurd part1 part2

theorem neg_neg_excludded_middle : Π p : Prop, ((p ∨ (p → false)) → false) → false :=
assume p : Prop,
assume hyp1, 
let subproof1 := assume hyp : p, hyp1 (or.intro_left (p → false) hyp) in
let subproof2 := or.intro_right p subproof1 in
hyp1 subproof2

theorem neg_neg_excludded_middle_2 : Π p : Prop, ((p ∨ (p → false)) → false) → false :=
assume p : Prop,
assume hyp1, 
hyp1 (or.intro_right p (assume hyp : p, hyp1 (or.intro_left (p → false) hyp)))

theorem neg_neg_excludded_middle_3 : Π p : Prop, ((p ∨ (p → false)) → false) → false :=
assume p : Prop,
assume f : (p ∨ (p → false)) → false, 
let subproof1  := assume g : p, f (or.intro_left (p → false) g) in
let subproof2 := or.intro_right p subproof1 in
f subproof2

end final_exercise

namespace curry_uncurry_execise

section 
    def curry (α β γ : Type) (f : α × β -> γ) : α -> β -> γ := λ (x : α) (y : β), f (x, y) 
    def uncurry (α β γ : Type) (f : α -> β -> γ) : α × β -> γ := λ (x : α × β), f x.1 x.2
end

end curry_uncurry_execise

namespace tutorial

variables p q r : Prop

theorem axiom1 : p -> q -> p := fun hp : p, fun hq : q, hp
theorem axiom1_again : p -> q -> p := fun (hp : p) (hq : q), hp
theorem axiom2 : (p -> (q -> r)) -> ((p -> q) -> (p -> r)) := 
    fun imp : (p -> (q -> r)), fun imp2 : (p -> q), fun hp : p, imp hp (imp2 hp)

theorem t1 : p -> q -> p := 
assume hp : p,
assume hq : q,
show p, from hp

theorem t1_again : forall (p q : Prop), p -> q -> p :=
    fun (p q : Prop) (hp : p) (hq : q), hp

example (hp : p) (hq : q) : p /\ q := and.intro hp hq
#check assume (hp : p) (hq : q), and.intro hp hq

example (h : p /\ q) : p := and.elim_left h

example (hp : p) : p \/ q := or.intro_left q hp
#check or.intro_left

example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (assume h : q ∧ p,
    show p ∧ q, from and.intro (and.right h) (and.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

lemma double_neg : p -> ¬¬ p := 
    fun hp : p, fun hp2 : ¬ p, hp2 hp

lemma swap_neg : (¬ p -> p) -> (¬ p -> ¬ ¬ p) := 
    fun hp1 : (¬ p -> p), fun hp2 : ¬ p, double_neg p (hp1 hp2)

theorem final_exercise : ¬ (p <-> ¬p) := 
assume h1 : (p <-> ¬ p), 
let part1 := fun hp : p, show false, from
    absurd (iff.elim_left h1 hp) (double_neg p hp) in
let part2 := fun hp : ¬p, show false, from 
    absurd hp (swap_neg p (iff.elim_right h1) hp) in
show false, from absurd part1 part2

theorem final_exercise_2 : ¬ (p <-> ¬p) := 
assume h1 : (p <-> ¬ p), 
let subproof1 := fun hp : p, (double_neg p hp) (iff.elim_left h1 hp) in
let subproof2 := fun hp : ¬p, (swap_neg p (iff.elim_right h1) hp) hp in
show false, from absurd subproof1 subproof2

theorem final_exercise_3 : ¬ (p <-> ¬p) := 
fun h1 : (p <-> ¬ p), 
(fun hp : ¬p, (swap_neg p (iff.elim_right h1) hp) hp) 
(fun hp : p, (double_neg p hp) (iff.elim_left h1 hp))

theorem final_exercise_4 : ¬ (p <-> ¬p) := 
fun h1 : (p <-> ¬ p), 
(fun hp : ¬p, (swap_neg p (iff.elim_right h1) hp) hp) 
(fun hp : p, (double_neg p hp) (iff.elim_left h1 hp))

universe u

inductive vector (α : Type u) : nat → Type u
| nil {} : vector 0
| cons : Π {n}, α → vector n → vector (n + 1)

namespace vector

local notation h :: t := cons h t

#check @vector.cases_on

end vector

example : 0 = 0 := rfl

end tutorial

