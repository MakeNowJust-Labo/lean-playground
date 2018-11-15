namespace hidden

universe u
variables {α : Type u}

inductive list (α : Type u)
| nil  {} : list
| cons : α → list → list

notation h :: t  := list.cons h t

namespace list
  def append (s t : list α) : list α :=
  list.rec t (λ x l u, x :: u) s

  instance list_has_append : has_append (list α) := ⟨append⟩

  lemma nil_append (t : list α) : nil ++ t = t := rfl

  lemma cons_append (x : α) (s t : list α) : (x :: s) ++ t = x :: (s ++ t) := rfl

  lemma append_nil (s : list α) : s ++ nil = s :=
  begin
    induction s with x s₁ ih,
    refl, -- case nil
    calc  -- case (x :: s₁)
      (x :: s₁) ++ nil = x :: (s₁ ++ nil) : rfl
                   ... = x :: s₁          : by rw ih
  end

  lemma append_assoc (s t u : list α) : s ++ (t ++ u) = (s ++ t) ++ u :=
  begin
    induction s with x s₁ ih,
    refl, -- case nil
    calc  -- case (x :: s₁)
      (x :: s₁) ++ (t ++ u) = x :: (s₁ ++ (t ++ u)) : rfl
                        ... = x :: ((s₁ ++ t) ++ u) : by rw ih
                        ... = ((x :: s₁) ++ t) ++ u : rfl
  end

  def reverse (s : list α) : list α :=
  list.rec_on s nil (λ x _ u, u ++ (x :: nil))

  lemma reverse_append (s t : list α) : reverse (s ++ t) = reverse t ++ reverse s :=
  begin
    induction s with x s₁ ih,
    calc -- case nil t
      reverse (nil ++ t) = reverse t                : rfl
                     ... = reverse t ++ nil         : by rw append_nil
                     ... = reverse t ++ reverse nil : rfl,
    calc -- case (x :: s₁) t
      reverse ((x :: s₁) ++ t) = reverse (s₁ ++ t) ++ reverse (x :: nil)         : rfl
                           ... = (reverse t ++ reverse s₁) ++ reverse (x :: nil) : by rw ih
                           ... = reverse t ++ (reverse s₁ ++ reverse (x :: nil)) : by rw append_assoc
                           ... = reverse t ++ reverse (x :: s₁)                  : rfl
  end

  lemma reverse_reverse (s : list α) : reverse (reverse s) = s :=
  begin
    induction s with x s₁ ih,
    refl, -- case nil
    calc  -- case (x :: s₁)
      reverse (reverse (x :: s₁)) = reverse (reverse ((x :: nil) ++ s₁))                 : rfl
                              ... = reverse (reverse s₁ ++ reverse (x :: nil))           : by rw reverse_append
                              ... = reverse (reverse (x :: nil)) ++ reverse (reverse s₁) : by rw reverse_append
                              ... = reverse (reverse (x :: nil)) ++ s₁                   : by rw ih
                              ... = x :: s₁                                              : rfl
  end

  def length (s : list α) : nat :=
  list.rec_on s 0 (λ x _ u, nat.succ u)

  lemma length_nil_eq_zero (s : list α) : length s = 0 → s = nil :=
  begin
    induction s; intros, refl, contradiction
  end

  lemma length_append (s t : list α) : length (s ++ t) = length s + length t :=
  begin
    induction s with x s₁ ih,
    calc -- case nil
      length (nil ++ t) = length t              : by rw nil_append
                    ... = length t + 0          : by rw nat_add_zero
                    ... = 0 + length t          : by rw nat.add_comm
                    ... = length nil + length t : rfl,
    calc -- case (x :: s₁)
      length ((x :: s₁) ++ t) = nat.succ (length (s₁ ++ t))     : rfl
                          ... = nat.succ (length s₁ + length t) : by rw ih
                          ... = nat.succ (length t + length s₁) : by rw nat.add_comm
                          ... = length t + nat.succ (length s₁) : by rw nat.add_succ
                          ... = length t + length (x :: s₁)     : rfl
                          ... = length (x :: s₁) + length t     : by rw nat.add_comm
  end

  lemma length_reverse (s : list α) : length (reverse s) = length s :=
  begin
    induction s with x s₁ ih,
    refl, -- case nil
    calc  -- case (x :: s₁)
      length (reverse (x :: s₁)) = length (reverse ((x :: nil) ++ s₁))       : rfl
                             ... = length (reverse s₁ ++ reverse (x :: nil)) : by rw reverse_append
                             ... = length (reverse s₁ ++ (x :: nil))         : rfl
                             ... = length (reverse s₁) + length (x :: nil)   : by rw length_append
                             ... = length s₁ + length (x :: nil)             : by rw ih
                             ... = length (x :: s₁)                          : rfl
  end
end list

end hidden
