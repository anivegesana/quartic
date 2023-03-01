import data.polynomial.basic
import data.polynomial.eval

namespace polynomial

variables {R : Type*} {a b c d e : R} [semiring R]

lemma degree_cubic_lt_degree_C_mul_X_cb (ha : a ≠ 0) :
  degree (C b * X ^ 3 + C c * X ^ 2 + C d * X + C e) < degree (C a * X ^ 4) :=
by simpa only [degree_C_mul_X_pow 4 ha] using degree_cubic_lt

@[simp] lemma leading_coeff_quartic (ha : a ≠ 0):
  leading_coeff (C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e) = a :=
by rw [add_assoc, add_assoc, add_assoc, ← add_assoc (C b * X ^ 3),
         ← add_assoc (C b * X ^ 3 + C c * X ^ 2), add_comm, leading_coeff_add_of_degree_lt $
         degree_cubic_lt_degree_C_mul_X_cb ha, leading_coeff_C_mul_X_pow]

lemma degree_quartic_le : degree (C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e) ≤ 4 :=
by simpa only [add_assoc] using degree_add_le_of_degree_le (degree_C_mul_X_pow_le 4 a)
  (le_trans degree_cubic_le $ with_bot.coe_le_coe.mpr $ nat.le_succ 3)

@[simp] lemma degree_quartic (ha : a ≠ 0) : degree (C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e) = 4 :=
begin
  rw [add_assoc, add_assoc, add_assoc, ← add_assoc (C b * X ^ 3),
         ← add_assoc (C b * X ^ 3 + C c * X ^ 2), degree_add_eq_left_of_degree_lt $
        degree_cubic_lt_degree_C_mul_X_cb ha, degree_C_mul_X_pow 4 ha],
  refl
end

@[simp] lemma nat_degree_quartic (ha : a ≠ 0) :
  nat_degree (C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e) = 4 :=
nat_degree_eq_of_degree_eq_some $ degree_quartic ha

end polynomial
