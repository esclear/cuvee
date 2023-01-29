theory list
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc []       a = a # []" |
  "snoc (x # xs) a = x # (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse []       = []" |
  "reverse (x # xs) = snoc (reverse xs) x"


lemma reverse_helper:
  "reverse (snoc l x) = x # (reverse l)"
  by (induction l) simp_all

lemma reverse_selfinverse:
  "reverse (reverse l) = l"
  by (induction l) (simp_all add: reverse_helper)
