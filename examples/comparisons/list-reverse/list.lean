def snoc {α : Type*} : list α → α → list α
  | []       x := [ x ]
  | (h :: t) x := h :: (snoc t x)

def reverse {α : Type*} : list α → list α
  | []       := []
  | (h :: t) := snoc (reverse t) h



theorem reverse_helper {α : Type*} : ∀ (x : α) (l : list α), reverse (snoc l x) = x :: (reverse l)
  | x []       := rfl
  | x (a :: l) := calc
    reverse (snoc (a :: l) x) = reverse (a :: snoc l x) : rfl
      ... = snoc (reverse (snoc l x)) a                 : rfl
      ... = snoc (x :: reverse l) a                     : congr_arg (λ k, snoc k a) (reverse_helper x l)
      ... = x :: reverse (a :: l)                       : rfl

theorem reverse_selfinverse {α : Type*} : ∀ (l : list α), reverse (reverse l) = l
  | []       := rfl
  | (a :: l) := trans
                  (reverse_helper a (reverse l))
                  (congr_arg (λ k, a :: k) (reverse_selfinverse l))



theorem reverse_helper_tac {α : Type*} : ∀ (x : α) (l : list α), reverse (snoc l x) = x :: (reverse l) :=
begin
  intros x l,
  induction l with a l,
  { refl },
  { have r : reverse (snoc l x) = x :: reverse l,
       by exact l_ih,
    show snoc (reverse (snoc l x)) a = snoc (x :: reverse l) a,
      congr,
      exact r }
end

theorem reverse_selfinverse_tac {α : Type*} : ∀ (l : list α), reverse (reverse l) = l :=
begin
  intro l,
  induction l with a l,
  { refl },
  { transitivity,
    exact reverse_helper_tac a (reverse l),
    congr,
    exact l_ih }
end

