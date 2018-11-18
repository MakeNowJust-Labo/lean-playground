universe u

inductive re (α : Type u) : Type u
| cat : re → re → re
| alt : re → re → re
| star : re → re
| char : α → re
| empty {} : re

variables {α : Type u}

def concat (Ls Lt : set (list α)) : set (list α) :=
--set.sUnion (set.image (λ s, set.image (λ t, s ++ t) Lt) Ls)
{u | ∃ (s ∈ Ls) (t ∈ Lt), u = s ++ t}

def repeatN (Ls : set (list α)) (n : ℕ) : set (list α) :=
nat.rec_on n
  {list.nil}               -- zero
  (λ n Ls₁, concat Ls₁ Ls) -- succ

def repeat (Ls : set (list α)) : set (list α) :=
  {a : list α | ∃ n : ℕ, a ∈ repeatN Ls n}
  -- set.sUnion (set.image (repeatN Ls) set.univ)

def L (r : re α) : set (list α) :=
re.rec_on r
  (λ s t Ls Lt, concat Ls Lt) -- cat
  (λ s t Ls Lt, Ls ∪ Lt)      -- alt
  (λ s Ls, repeat Ls)         -- star
  (λ x, {[x]})                -- char
  ∅                           -- empty

example : L (@re.empty α) = ∅ := rfl

lemma mem_singleton_x : ∀ (x : α), x ∈ (singleton x : set α) :=
begin
  intros,
  simp [singleton, set.insert],
  left, refl
end

lemma mem_singleton_eq : ∀ (x y : α), x ∈ ({y} : set α) ↔ (x = y) :=
begin
  intros x y,
  rw calc x ∈ ({y} : set α) = (λ a, a = y ∨ a ∈ ∅) x : rfl
                        ... = (x = y ∨ x ∈ ∅)        : rfl,
  apply or_iff_left_of_imp,
  rw calc x ∈ (∅ : set α) = (λ x, false) x : rfl
                      ... = false          : rfl,
  contradiction
end

lemma mem_repeat0_nil : ∀ (Ls : set (list α)), list.nil ∈ repeatN Ls 0 :=
begin
  intros,
  simp [repeatN],
  apply mem_singleton_x
end

lemma mem_repeat_nil : ∀ Ls : set (list α), list.nil ∈ repeat Ls :=
begin
  intros,
  rw repeat,
  existsi 0,
  apply mem_repeat0_nil

  /-
  -- repeat Ls = set.sUnion (set.image (repeatN Ls) set.univ) version
  intro Ls,
  rw [repeat, set.sUnion, set.image],
  existsi repeatN Ls 0,
  existsi _,
  apply mem_repeat0_nil Ls,
  existsi 0,
  constructor, rw set.has_mem, simp
  -/
end

lemma concat_nil : ∀ Ls : set (list α), concat {list.nil} Ls = Ls :=
begin
  intros Ls,
  rw concat,
  apply funext,
  intros x,
  apply propext,
  apply iff.intro,
  show Ls x → _, intros H,
    existsi [list.nil, _, x, H],
    refl,
    left, refl,
  show _ → Ls x, intros H₁,
    apply exists.elim H₁, intros a H₂,
    apply exists.elim H₂, intros ha H₃,
    apply exists.elim H₃, intros b H₄,
    apply exists.elim H₄, intros hb H₅,
    have a_eq_nil := iff.elim_left (mem_singleton_eq a list.nil) ha,
    simp [a_eq_nil] at H₅,
    rw H₅,
    exact hb
end

lemma nil_concat : ∀ Ls : set (list α), concat Ls {list.nil} = Ls :=
begin
  intros Ls,
  rw concat,
  apply funext,
  intros x,
  apply propext,
  apply iff.intro,
  show Ls x → _, intros H,
    existsi [x, H, list.nil, _],
    rw list.append_nil,
    left, refl,
  show _ → Ls x, intros H₁,
    apply exists.elim H₁, intros a H₂,
    apply exists.elim H₂, intros ha H₃,
    apply exists.elim H₃, intros b H₄,
    apply exists.elim H₄, intros hb H₅,
    have b_eq_nil := iff.elim_left (mem_singleton_eq b list.nil) hb,
    simp [b_eq_nil] at H₅,
    rw H₅,
    exact ha
end

lemma concat_assoc : ∀ Ls Lt Lu : set (list α), concat Ls (concat Lt Lu) = concat (concat Ls Lt) Lu :=
begin
  intros Ls Lt Lu,
  simp [concat],
  apply funext,
  intros x,
  apply propext,
  apply iff.intro,
  intros H₁,
    apply exists.elim H₁, intros a H₂,
    apply exists.elim H₂, intros ha H₃,
    apply exists.elim H₃, intros bc H₄,
    apply exists.elim H₄, intros hbc H₅,
    apply exists.elim hbc, intros b H₆,
    apply exists.elim H₆, intros hb H₇,
    apply exists.elim H₇, intros c H₈,
    apply exists.elim H₈, intros hc H₉,
    existsi a ++ b, existsi _,
    existsi c, existsi hc,
    rw [list.append_assoc, ←H₉], exact H₅,
    existsi a, existsi ha,
    existsi b, existsi hb, refl,
  intros H₁,
    apply exists.elim H₁, intros ab H₂,
    apply exists.elim H₂, intros hab H₃,
    apply exists.elim H₃, intros c H₄,
    apply exists.elim H₄, intros hc H₅,
    apply exists.elim hab, intros a H₆,
    apply exists.elim H₆, intros ha H₇,
    apply exists.elim H₇, intros b H₈,
    apply exists.elim H₈, intros hb H₉,
    existsi a, existsi ha,
    existsi b ++ c, existsi _,
    rw [←list.append_assoc, ←H₉], exact H₅,
    existsi b, existsi hb,
    existsi c, existsi hc, refl
end

lemma repeatN_succ : ∀ (Ls : set (list α)) (n : ℕ), repeatN Ls (nat.succ n) = concat (repeatN Ls n) Ls :=
begin
  intros Ls n,
  calc repeatN Ls (nat.succ n) = concat (repeatN Ls n) Ls : rfl
end

lemma repeatN_plus : ∀ (Ls : set (list α)) (n m : ℕ), concat (repeatN Ls n) (repeatN Ls m) = repeatN Ls (n + m) :=
begin
  intros Ls n m,
  induction m with m₁ ih,
  simp, apply nil_concat,
  simp [repeatN_succ],
  rw ←ih,
  apply concat_assoc
end
