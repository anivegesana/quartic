import data.polynomial.basic
import data.polynomial.eval
import data.polynomial.identities
import data.polynomial.splits

import data.polynomial.nat_degree_quartic
import algebra.quartic_discriminant.card_eq_four

noncomputable theory


@[ext] structure quartic (R : Type*) := (a b c d e : R)


namespace quartic

open quartic polynomial

open_locale polynomial

variables {R S F K : Type*}

instance [inhabited R] : inhabited (quartic R) := ⟨⟨default, default, default, default, default⟩⟩

instance [has_zero R] : has_zero (quartic R) := ⟨⟨0, 0, 0, 0, 0⟩⟩

section basic

variables {P Q : quartic R} {a b c d e a' b' c' d' e' : R} [semiring R]

/-- Convert a quartic polynomial to a polynomial. -/
def to_poly (P : quartic R) : R[X] := C P.a * X ^ 4 + C P.b * X ^ 3 + C P.c * X ^ 2 + C P.d * X + C P.e

theorem C_mul_prod_X_sub_C_eq [comm_ring S] {v w x y z : S} :
  C v * (X - C w) * (X - C x) * (X - C y) * (X - C z)
    = to_poly ⟨v, v * -(w + x + y + z), v * (w * x + w * y + w * z + x * y + x * z + y * z), v * -(w * x * y + w * x * z + w * y * z + x * y * z), v * (w * x * y * z)⟩ :=
by { simp only [to_poly, C_neg, C_add, C_mul], ring1 }

theorem prod_X_sub_C_eq [comm_ring S] {w x y z : S} :
  (X - C w) * (X - C x) * (X - C y) * (X - C z)
    = to_poly ⟨1, -(w + x + y + z), (w * x + w * y + w * z + x * y + x * z + y * z), -(w * x * y + w * x * z + w * y * z + x * y * z), (w * x * y * z)⟩ :=
by rw [← one_mul $ X - C w, ← C_1, C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul, one_mul ]

/-! ### Coefficients -/

section coeff

private lemma coeffs :
  (∀ n > 4, P.to_poly.coeff n = 0) ∧ P.to_poly.coeff 4 = P.a ∧ P.to_poly.coeff 3 = P.b
    ∧ P.to_poly.coeff 2 = P.c ∧ P.to_poly.coeff 1 = P.d ∧ P.to_poly.coeff 0 = P.e :=
begin
  simp only [to_poly, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow],
  norm_num,
  intros n hn,
  repeat { rw [if_neg] },
  any_goals { linarith only [hn] },
  repeat { rw [zero_add] }
end

@[simp] lemma coeff_eq_zero {n : ℕ} (hn : 4 < n) : P.to_poly.coeff n = 0 := coeffs.1 n hn

@[simp] lemma coeff_eq_a : P.to_poly.coeff 4 = P.a := coeffs.2.1

@[simp] lemma coeff_eq_b : P.to_poly.coeff 3 = P.b := coeffs.2.2.1

@[simp] lemma coeff_eq_c : P.to_poly.coeff 2 = P.c := coeffs.2.2.2.1

@[simp] lemma coeff_eq_d : P.to_poly.coeff 1 = P.d := coeffs.2.2.2.2.1

@[simp] lemma coeff_eq_e : P.to_poly.coeff 0 = P.e := coeffs.2.2.2.2.2

lemma a_of_eq (h : P.to_poly = Q.to_poly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]

lemma b_of_eq (h : P.to_poly = Q.to_poly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]

lemma c_of_eq (h : P.to_poly = Q.to_poly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]

lemma d_of_eq (h : P.to_poly = Q.to_poly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]

lemma e_of_eq (h : P.to_poly = Q.to_poly) : P.e = Q.e := by rw [← coeff_eq_e, h, coeff_eq_e]

lemma to_poly_injective (P Q : quartic R) : P.to_poly = Q.to_poly ↔ P = Q :=
⟨λ h, ext P Q (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h) (e_of_eq h), congr_arg to_poly⟩

lemma of_a_eq_zero (ha : P.a = 0) : P.to_poly = C P.b * X ^ 3 + C P.c * X ^ 2 + C P.d * X + C P.e :=
by rw [to_poly, ha, C_0, zero_mul, zero_add]

lemma of_a_eq_zero' : to_poly ⟨0, b, c, d, e⟩ = C b * X ^ 3 + C c * X ^ 2 + C d * X + C e := of_a_eq_zero rfl 

lemma of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly = C P.c * X ^ 2 + C P.d * X + C P.e :=
by rw [of_a_eq_zero ha, hb, C_0, zero_mul, zero_add]

lemma of_b_eq_zero' : to_poly ⟨0, 0, c, d, e⟩ = C c * X ^ 2 + C d * X + C e := of_b_eq_zero rfl rfl

lemma of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.to_poly = C P.d * X + C P.e :=
by rw [of_b_eq_zero ha hb, hc, C_0, zero_mul, zero_add]

lemma of_c_eq_zero' : to_poly ⟨0, 0, 0, d, e⟩ = C d * X + C e := of_c_eq_zero rfl rfl rfl

lemma of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
  P.to_poly = C P.e :=
by rw [of_c_eq_zero ha hb hc, hd, C_0, zero_mul, zero_add]

lemma of_d_eq_zero' : to_poly ⟨0, 0, 0, 0, e⟩ = C e := of_d_eq_zero rfl rfl rfl rfl

lemma of_e_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) (he : P.e = 0) :
  P.to_poly = 0 :=
by rw [of_d_eq_zero ha hb hc hd, he, C_0]

lemma of_e_eq_zero' : (⟨0, 0, 0, 0, 0⟩ : quartic R).to_poly = 0 := of_e_eq_zero rfl rfl rfl rfl rfl

lemma zero : (0 : quartic R).to_poly = 0 := of_e_eq_zero'

lemma to_poly_eq_zero_iff (P : quartic R) : P.to_poly = 0 ↔ P = 0 :=
by rw [← zero, to_poly_injective]

private lemma ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0 ∨ P.e ≠ 0) : P.to_poly ≠ 0 :=
by { contrapose! h0, rw [(to_poly_eq_zero_iff P).mp h0], exact ⟨rfl, rfl, rfl, rfl, rfl⟩ }

lemma ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly ≠ 0 := (or_imp_distrib.mp ne_zero).1 ha

lemma ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).1 hb

lemma ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).1 hc

lemma ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).2).1 hd

lemma ne_zero_of_e_ne_zero (he : P.e ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).2).2 he

@[simp] lemma leading_coeff_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.leading_coeff = P.a :=
leading_coeff_quartic ha

@[simp] lemma leading_coeff_of_a_ne_zero' (ha : a ≠ 0) : (to_poly ⟨a, b, c, d, e⟩).leading_coeff = a :=
leading_coeff_of_a_ne_zero ha

@[simp] lemma leading_coeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) :
  P.to_poly.leading_coeff = P.b :=
by rw [of_a_eq_zero ha, leading_coeff_cubic hb]

@[simp] lemma leading_coeff_of_b_ne_zero' (hb : b ≠ 0) : (to_poly ⟨0, b, c, d, e⟩).leading_coeff = b :=
leading_coeff_of_b_ne_zero rfl hb

@[simp] lemma leading_coeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.leading_coeff = P.c :=
by rw [of_b_eq_zero ha hb, leading_coeff_quadratic hc]

@[simp] lemma leading_coeff_of_c_ne_zero' (hc : c ≠ 0) : (to_poly ⟨0, 0, c, d, e⟩).leading_coeff = c :=
leading_coeff_of_c_ne_zero rfl rfl hc

@[simp] lemma leading_coeff_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
  P.to_poly.leading_coeff = P.d :=
by rw [of_c_eq_zero ha hb hc, leading_coeff_linear hd]

@[simp] lemma leading_coeff_of_d_ne_zero' (hd : d ≠ 0) : (to_poly ⟨0, 0, 0, d, e⟩).leading_coeff = d :=
leading_coeff_of_d_ne_zero rfl rfl rfl hd

@[simp] lemma leading_coeff_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
  P.to_poly.leading_coeff = P.e :=
by rw [of_d_eq_zero ha hb hc hd, leading_coeff_C]

@[simp] lemma leading_coeff_of_d_eq_zero' : (to_poly ⟨0, 0, 0, 0, e⟩).leading_coeff = e :=
leading_coeff_of_d_eq_zero rfl rfl rfl rfl

lemma monic_of_a_eq_one (ha : P.a = 1) : P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_a_ne_zero $ by { rw [ha], exact one_ne_zero }, ha]
end

lemma monic_of_a_eq_one' : (to_poly ⟨1, b, c, d, e⟩).monic := monic_of_a_eq_one rfl

lemma monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_b_ne_zero ha $ by { rw [hb], exact one_ne_zero }, hb]
end

lemma monic_of_b_eq_one' : (to_poly ⟨0, 1, c, d, e⟩).monic := monic_of_b_eq_one rfl rfl

lemma monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_c_ne_zero ha hb $ by { rw [hc], exact one_ne_zero }, hc]
end

lemma monic_of_c_eq_one' : (to_poly ⟨0, 0, 1, d, e⟩).monic := monic_of_c_eq_one rfl rfl rfl

lemma monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
  P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_d_ne_zero ha hb hc $ by { rw [hd], exact one_ne_zero }, hd]
end

lemma monic_of_d_eq_one' : (to_poly ⟨0, 0, 0, 1, e⟩).monic := monic_of_d_eq_one rfl rfl rfl rfl

lemma monic_of_e_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) (he : P.e = 1) :
  P.to_poly.monic :=
by rw [monic, leading_coeff_of_d_eq_zero ha hb hc hd, he]

lemma monic_of_e_eq_one' : (to_poly ⟨0, 0, 0, 0, 1⟩).monic := monic_of_e_eq_one rfl rfl rfl rfl rfl

end coeff

/-! ### Degrees -/

section degree

/-- The equivalence between quartic polynomials and polynomials of degree at most four. -/
@[simps] def equiv : quartic R ≃ {p : R[X] // p.degree ≤ 4} :=
{ to_fun    := λ P, ⟨P.to_poly, degree_quartic_le⟩,
  inv_fun   := λ f, ⟨coeff f 4, coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩,
  left_inv  := λ P, by ext; simp only [subtype.coe_mk, coeffs],
  right_inv := λ f,
  begin
    ext (_ | _ | _ | _ | _ | n); simp only [subtype.coe_mk, coeffs],
    have h4 : 4 < n + 5 := by linarith only,
    rw [coeff_eq_zero h4,
        (degree_le_iff_coeff_zero (f : R[X]) 4).mp f.2 _ $ with_bot.coe_lt_coe.mpr h4]
  end }

@[simp] lemma degree_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.degree = 4 := degree_quartic ha

@[simp] lemma degree_of_a_ne_zero' (ha : a ≠ 0) : (to_poly ⟨a, b, c, d, e⟩).degree = 4 :=
degree_of_a_ne_zero ha

lemma degree_of_a_eq_zero (ha : P.a = 0) : P.to_poly.degree ≤ 3 :=
by simpa only [of_a_eq_zero ha] using degree_cubic_le

lemma degree_of_a_eq_zero' : (to_poly ⟨0, b, c, d, e⟩).degree ≤ 3 := degree_of_a_eq_zero rfl

@[simp] lemma degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.to_poly.degree = 3 :=
by rw [of_a_eq_zero ha, degree_cubic hb]

@[simp] lemma degree_of_b_ne_zero' (hb : b ≠ 0) : (to_poly ⟨0, b, c, d, e⟩).degree = 3 :=
degree_of_b_ne_zero rfl hb

lemma degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly.degree ≤ 2 :=
by simpa only [of_b_eq_zero ha hb] using degree_quadratic_le

lemma degree_of_b_eq_zero' : (to_poly ⟨0, 0, c, d, e⟩).degree ≤ 2 := degree_of_b_eq_zero rfl rfl

@[simp] lemma degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.degree = 2 :=
by rw [of_b_eq_zero ha hb, degree_quadratic hc]

@[simp] lemma degree_of_c_ne_zero' (hc : c ≠ 0) : (to_poly ⟨0, 0, c, d, e⟩).degree = 2 :=
degree_of_c_ne_zero rfl rfl hc

lemma degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.to_poly.degree ≤ 1 :=
by simpa only [of_c_eq_zero ha hb hc] using degree_linear_le

lemma degree_of_c_eq_zero' : (to_poly ⟨0, 0, 0, d, e⟩).degree ≤ 1 := degree_of_c_eq_zero rfl rfl rfl

@[simp] lemma degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
  P.to_poly.degree = 1 :=
by rw [of_c_eq_zero ha hb hc, degree_linear hd]

@[simp] lemma degree_of_d_ne_zero' (hd : d ≠ 0) : (to_poly ⟨0, 0, 0, d, e⟩).degree = 1 :=
degree_of_d_ne_zero rfl rfl rfl hd

lemma degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) : P.to_poly.degree ≤ 0 :=
by simpa only [of_d_eq_zero ha hb hc hd] using degree_C_le

lemma degree_of_d_eq_zero' : (to_poly ⟨0, 0, 0, 0, e⟩).degree ≤ 0 := degree_of_d_eq_zero rfl rfl rfl rfl

@[simp] lemma degree_of_e_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) (he : P.e ≠ 0) :
  P.to_poly.degree = 0 :=
by rw [of_d_eq_zero ha hb hc hd, degree_C he]

@[simp] lemma degree_of_e_ne_zero' (he : e ≠ 0) : (to_poly ⟨0, 0, 0, 0, e⟩).degree = 0 :=
degree_of_e_ne_zero rfl rfl rfl rfl he

@[simp] lemma degree_of_e_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) (he : P.e = 0) :
  P.to_poly.degree = ⊥ :=
by rw [of_e_eq_zero ha hb hc hd he, degree_zero]

@[simp] lemma degree_of_e_eq_zero' : (⟨0, 0, 0, 0, 0⟩ : quartic R).to_poly.degree = ⊥ :=
degree_of_e_eq_zero rfl rfl rfl rfl rfl

@[simp] lemma degree_of_zero : (0 : quartic R).to_poly.degree = ⊥ := degree_of_e_eq_zero'

@[simp] lemma nat_degree_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.nat_degree = 4 :=
nat_degree_quartic ha

@[simp] lemma nat_degree_of_a_ne_zero' (ha : a ≠ 0) : (to_poly ⟨a, b, c, d, e⟩).nat_degree = 4 :=
nat_degree_of_a_ne_zero ha

lemma nat_degree_of_a_eq_zero (ha : P.a = 0) : P.to_poly.nat_degree ≤ 3 :=
by simpa only [of_a_eq_zero ha] using nat_degree_cubic_le

lemma nat_degree_of_a_eq_zero' : (to_poly ⟨0, b, c, d, e⟩).nat_degree ≤ 3 :=
nat_degree_of_a_eq_zero rfl

@[simp] lemma nat_degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.to_poly.nat_degree = 3 :=
by rw [of_a_eq_zero ha, nat_degree_cubic hb]

@[simp] lemma nat_degree_of_b_ne_zero' (hb : b ≠ 0) : (to_poly ⟨0, b, c, d, e⟩).nat_degree = 3 :=
nat_degree_of_b_ne_zero rfl hb

lemma nat_degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly.nat_degree ≤ 2 :=
by simpa only [of_b_eq_zero ha hb] using nat_degree_quadratic_le

lemma nat_degree_of_b_eq_zero' : (to_poly ⟨0, 0, c, d, e⟩).nat_degree ≤ 2 :=
nat_degree_of_b_eq_zero rfl rfl

@[simp] lemma nat_degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.nat_degree = 2 :=
by rw [of_b_eq_zero ha hb, nat_degree_quadratic hc]

@[simp] lemma nat_degree_of_c_ne_zero' (hc : c ≠ 0) : (to_poly ⟨0, 0, c, d, e⟩).nat_degree = 2 :=
nat_degree_of_c_ne_zero rfl rfl hc

lemma nat_degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
  P.to_poly.nat_degree ≤ 1 :=
by rw [of_c_eq_zero ha hb hc, nat_degree_linear hd]

lemma nat_degree_of_c_eq_zero' (hd : d ≠ 0) : (to_poly ⟨0, 0, 0, d, e⟩).nat_degree ≤ 1 :=
nat_degree_of_c_eq_zero rfl rfl rfl hd

@[simp] lemma nat_degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
  P.to_poly.nat_degree = 1 :=
by rw [of_c_eq_zero ha hb hc, nat_degree_linear hd]

@[simp] lemma nat_degree_of_d_ne_zero' (hd : d ≠ 0) : (to_poly ⟨0, 0, 0, d, e⟩).nat_degree = 1 :=
nat_degree_of_d_ne_zero rfl rfl rfl hd

@[simp] lemma nat_degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
  P.to_poly.nat_degree = 0 :=
by rw [of_d_eq_zero ha hb hc hd, nat_degree_C]

@[simp] lemma nat_degree_of_d_eq_zero' : (to_poly ⟨0, 0, 0, 0, e⟩).nat_degree = 0 :=
nat_degree_of_d_eq_zero rfl rfl rfl rfl

@[simp] lemma nat_degree_of_zero : (0 : quartic R).to_poly.nat_degree = 0 := nat_degree_of_d_eq_zero'

end degree

section map

variables [semiring S] {φ : R →+* S}

/-- Map a quartic polynomial across a semiring homomorphism. -/
def map (φ : R →+* S) (P : quartic R) : quartic S := ⟨φ P.a, φ P.b, φ P.c, φ P.d, φ P.e⟩

lemma map_to_poly : (map φ P).to_poly = polynomial.map φ P.to_poly :=
by simp only [map, to_poly, map_C, map_X, polynomial.map_add, polynomial.map_mul,
              polynomial.map_pow]

end map

end basic

section roots

open multiset

/-! ### Roots over an extension -/

section extension

variables {P : quartic R} [comm_ring R] [comm_ring S] {φ : R →+* S}

/-- The roots of a cubic polynomial. -/
def roots [is_domain R] (P : quartic R) : multiset R := P.to_poly.roots

lemma map_roots [is_domain S] : (map φ P).roots = (polynomial.map φ P.to_poly).roots :=
by rw [roots, map_to_poly]

theorem mem_roots_iff [is_domain R] (h0 : P.to_poly ≠ 0) (x : R) :
  x ∈ P.roots ↔ P.a * x ^ 4 + P.b * x ^ 3 + P.c * x ^ 2 + P.d * x + P.e = 0 :=
begin
  rw [roots, mem_roots h0, is_root, to_poly],
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
end

theorem card_roots_le [is_domain R] [decidable_eq R] : P.roots.to_finset.card ≤ 4 :=
begin
  apply (to_finset_card_le P.to_poly.roots).trans,
  by_cases hP : P.to_poly = 0,
  { exact (card_roots' P.to_poly).trans (by { rw [hP, nat_degree_zero], exact zero_le 4 }) },
  { exact with_bot.coe_le_coe.1 ((card_roots hP).trans degree_quartic_le) }
end

end extension

variables {P : quartic F} [field F] [field K] {φ : F →+* K} {w x y z : K}

/-! ### Roots over a splitting field -/

section split

theorem splits_iff_card_roots (ha : P.a ≠ 0) : splits φ P.to_poly ↔ (map φ P).roots.card = 4 :=
begin
  replace ha : (map φ P).a ≠ 0 := (_root_.map_ne_zero φ).mpr ha,
  nth_rewrite_lhs 0 [← ring_hom.id_comp φ],
  rw [roots, ← splits_map_iff, ← map_to_poly, splits_iff_card_roots,
      ← ((degree_eq_iff_nat_degree_eq $ ne_zero_of_a_ne_zero ha).mp $
          degree_of_a_ne_zero ha : _ = 4)]
end

theorem splits_iff_roots_eq_four (ha : P.a ≠ 0) :
  splits φ P.to_poly ↔ ∃ w x y z : K, (map φ P).roots = {w, x, y, z} :=
by rw [splits_iff_card_roots ha, multiset.card_eq_four]

theorem eq_prod_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  (map φ P).to_poly = C (φ P.a) * (X - C w) * (X - C x) * (X - C y) * (X - C z) :=
begin
  rw [map_to_poly, eq_prod_roots_of_splits $ (splits_iff_roots_eq_four ha).mpr $ exists.intro w $
        exists.intro x $ exists.intro y $ exists.intro z h4, leading_coeff_of_a_ne_zero ha, ← map_roots, h4],
  change C (φ P.a) * ((X - C w) ::ₘ (X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _,
  rw [prod_cons, prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc, mul_assoc]
end

theorem eq_sum_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  map φ P = ⟨φ P.a, φ P.a * -(w + x + y + z), φ P.a * (w * x + w * y + w * z + x * y + x * z + y * z), φ P.a * -(w * x * y + w * x * z + w * y * z + x * y * z), φ P.a * (w * x * y * z)⟩ :=
begin
  apply_fun to_poly,
  any_goals { exact λ P Q, (to_poly_injective P Q).mp },
  rw [eq_prod_four_roots ha h4, C_mul_prod_X_sub_C_eq]
end

theorem b_eq_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  φ P.b = φ P.a * -(w + x + y + z) :=
by injection eq_sum_four_roots ha h4

theorem c_eq_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  φ P.c = φ P.a * (w * x + w * y + w * z + x * y + x * z + y * z) :=
by injection eq_sum_four_roots ha h4

theorem d_eq_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  φ P.d = φ P.a * -(w * x * y + w * x * z + w * y * z + x * y * z) :=
by injection eq_sum_four_roots ha h4

theorem e_eq_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  φ P.e = φ P.a * (w * x * y * z) :=
by injection eq_sum_four_roots ha h4

end split


/-! ### Discriminant over a splitting field -/

section discriminant

def discP {R : Type*} [ring R] (P : quartic R) : R := 8 * P.a * P.c - 3 * P.b ^ 2
def discR {R : Type*} [ring R] (P : quartic R) : R := P.b ^ 3 + 8 * P.d * P.a ^ 2 - 4 * P.a * P.b * P.c
def discΔ_0 {R : Type*} [ring R] (P : quartic R) : R := P.c ^ 2 - 3 * P.b * P.d + 12 * P.a * P.e
def discD {R : Type*} [ring R] (P : quartic R) : R := 64 * P.a ^ 3 * P.e - 16 * P.a ^ 2 * P.c ^ 2 + 16 * P.a * P.b ^ 2 * P.c - 16 * P.a ^ 2 * P.b * P.d - 3 * P.b ^ 4

/-- The discriminant of a quartic polynomial. -/
def disc {R : Type*} [ring R] (P : quartic R) : R :=
256 * P.a^3 * P.e^3-192 * P.a^2 * P.b * P.d * P.e^2-128 * P.a^2 * P.c^2 * P.e^2+144 * P.a^2 * P.c * P.d^2 * P.e-27 * P.a^2 * P.d^4+144 * P.a * P.b^2 * P.c * P.e^2-6 * P.a * P.b^2 * P.d^2 * P.e-80 * P.a * P.b * P.c^2 * P.d * P.e+18 * P.a * P.b * P.c * P.d^3+16 * P.a * P.c^4 * P.e-4 * P.a * P.c^3 * P.d^2-27 * P.b^4 * P.e^2+18 * P.b^3 * P.c * P.d * P.e-4 * P.b^3 * P.d^3-4 * P.b^2 * P.c^3 * P.e+  P.b^2 * P.c^2 * P.d^2

theorem disc_eq_prod_four_roots (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  φ P.disc = (φ P.a * φ P.a * φ P.a * (w - x) * (w - y) * (w - z) * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_four_roots ha h4, c_eq_four_roots ha h4, d_eq_four_roots ha h4, e_eq_four_roots ha h4],
  ring1
end

theorem disc_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  P.disc ≠ 0 ↔ w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z :=
begin
  rw [←_root_.map_ne_zero φ, disc_eq_prod_four_roots ha h4, pow_two],
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self, and_iff_right ha, and_assoc],
end

theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h4 : (map φ P).roots = {w, x, y, z}) :
  P.disc ≠ 0 ↔ (map φ P).roots.nodup :=
begin
  rw [disc_ne_zero_iff_roots_ne ha h4, h4],
  change _ ↔ (w ::ₘ x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, nodup_cons, mem_cons, mem_cons, mem_cons, mem_singleton, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem card_roots_of_disc_ne_zero [decidable_eq K] (ha : P.a ≠ 0)
  (h3 : (map φ P).roots = {w, x, y, z}) (hd : P.disc ≠ 0) : (map φ P).roots.to_finset.card = 4 :=
begin
  rw [to_finset_card_of_nodup $ (disc_ne_zero_iff_roots_nodup ha h3).mp hd,
      ← splits_iff_card_roots ha, splits_iff_roots_eq_four ha],
  exact ⟨w, ⟨x, ⟨y, ⟨z, h3⟩⟩⟩⟩
end

end discriminant

end roots

end quartic
