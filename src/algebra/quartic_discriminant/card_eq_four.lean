import data.finset.basic
import data.finset.card

import data.list.basic

import data.multiset.basic

namespace finset

variables {α β : Type*}
variables {s t : finset α} {a b : α}

lemma card_eq_four [decidable_eq α] :
  s.card = 4 ↔ ∃ w x y z, w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {w, x, y, z} :=
begin
  split,
  { rw card_eq_succ,
    simp_rw [card_eq_three],
    rintro ⟨a, _, abcd, rfl, b, c, d, bc, bd, cd, rfl⟩,
    rw [mem_insert, not_or_distrib, mem_insert, mem_singleton, not_or_distrib] at abcd,
    exact ⟨a, b, c, d, abcd.1, abcd.2.1, abcd.2.2, bc, bd, cd, rfl⟩ },
  { rintro ⟨w, x, y, z, wx, wy, wz, xy, xz, yz, rfl⟩,
    simp only [wx, wy, wz, xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton,
      or_self, card_singleton] }
end

end finset


namespace list

variable {α : Type*}

lemma length_eq_four {l : list α} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
⟨match l with [a, b, c, d], _ := ⟨a, b, c, d, rfl⟩ end, λ ⟨a, b, c, d, e⟩, e.symm ▸ rfl⟩

end list


namespace multiset

variable {α : Type*}

lemma card_eq_four {s : multiset α} : s.card = 4 ↔ ∃ w x y z, s = {w, x, y, z} :=
⟨quot.induction_on s (λ l h, (list.length_eq_four.mp h).imp
  (λ a, Exists.imp (λ b, Exists.imp (λ c, Exists.imp (λ d, congr_arg coe))))), λ ⟨a, b, c, d, e⟩, e.symm ▸ rfl⟩

end multiset
