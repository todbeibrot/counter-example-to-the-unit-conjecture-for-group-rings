import HW

mk_simp_attribute pm_one_simp "simp lemmas for pm and sign'"

inductive pm : Type
| one : pm
| mone : pm

def pm_one (x : pm) : ℚ :=
pm.rec_on x 1 (-1)

namespace pm

protected def mul : pm → pm → pm
| one one := one
| mone one := mone
| one mone := mone
| mone mone := one

instance : has_mul pm := ⟨pm.mul⟩

@[pm_one_simp, simp] lemma one_mul_one : one * one = one := rfl

@[pm_one_simp, simp] lemma mone_mul_one : mone * one = mone := rfl

@[pm_one_simp, simp] lemma one_mul_mone : one * mone = mone := rfl

@[pm_one_simp, simp] lemma mone_mul_mone : mone * mone = one := rfl

@[pm_one_simp, simp] lemma pm_one_one : 
pm_one pm.one = 1 := rfl

@[pm_one_simp, simp] lemma pm_one_mone : 
pm_one pm.mone = -1 := rfl

@[pm_one_simp, simp] lemma pm_one_inv (x : pm) : 
(pm_one x)⁻¹ = pm_one x := by cases x; field_simp

@[pm_one_simp, simp] lemma pm_one_sq (x : pm) : 
pm_one x * pm_one x = 1 := 
begin
  cases x,
  simp only [pm_one_one, mul_one],
  simp only [pm_one_mone, mul_neg, mul_one, neg_neg],
end

@[pm_one_simp, simp] lemma pm_one_mul (x1 x2 : pm) : 
pm_one (x1 * x2) = (pm_one x1) * (pm_one x2)   := by cases x1; cases x2; simp with pm_one_simp

@[pm_one_simp, simp] lemma mul_one (x : pm) :
x * one = x := by cases x; simp

@[pm_one_simp, simp] lemma one_mul (x : pm) :
one * x = x := by cases x; simp

@[pm_one_simp, simp] lemma pm_one_mone_mul (x : pm) :
pm_one (mone * x) = pm_one x * -1 := by cases x; simp

@[pm_one_simp, simp] lemma pm_one_mul_mone (x : pm) :
pm_one (x * mone) = -1 * pm_one x := by cases x; simp

--pos → one, neg → mone
def sign' : ℚ → pm :=
begin
  intro q,
  cases q.num with pos neg,
  exact one,
  exact mone
end

@[pm_one_simp, simp] lemma sign'_one : sign' 1 = one := rfl

@[pm_one_simp, simp] lemma sign'_neg_one : sign' (-1) = mone := rfl

@[pm_one_simp, simp] lemma sign'_pm_one (x: pm) : sign' (pm_one x) = x := 
by cases x; simp only with pm_one_simp

@[pm_one_simp, simp] lemma sign'_not_neg {x : ℚ} (x_pos : 0 ≤ x) : sign'(x) = one :=
begin
  have x_pos' : 0 ≤ x.num,
  { exact rat.num_nonneg_iff_zero_le.mpr x_pos },
  unfold sign',
  cases x.num with pos neg,
  { simp only },
  { contrapose x_pos',
    simp only [int.neg_succ_not_nonneg, not_false_iff] }
end

@[pm_one_simp, simp] lemma sign'_pos {x : ℚ} (x_pos : 0 < x) : sign'(x) = one :=
begin
  have x_pos' : 0 < x.num,
  { exact rat.num_pos_iff_pos.mpr x_pos },
  unfold sign',
  cases x.num with pos neg,
  { simp only },
  { contrapose x_pos',
    simp only [int.neg_succ_not_pos, not_false_iff] }
end

@[pm_one_simp, simp] lemma sign'_neg {x : ℚ} (x_neg : x < 0) : sign'(x) = mone :=
begin
  have x_neg' : x.num < 0,
  { rw rat.lt_def at x_neg,
    simp only [int.mul_one, rat.denom_zero, int.coe_nat_zero, zero_mul, int.coe_nat_succ,
      zero_add, rat.num_zero] at x_neg,
    exact x_neg },
  unfold sign',
  cases x.num with pos neg,
  { contrapose x_neg',
    simp only [not_lt, int.coe_nat_nonneg, int.of_nat_eq_coe]},
  { simp only }
end

@[pm_one_simp, simp] lemma sign'_mul {x y : ℚ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
sign' (x * y) = sign'(x) * sign'(y) :=
begin
  cases (ne.lt_or_lt hx0) with xneg xpos; cases (ne.lt_or_lt hy0) with yneg ypos,
  { rw [sign'_neg xneg, sign'_neg yneg, sign'_pos (mul_pos_of_neg_of_neg xneg yneg), mone_mul_mone] },
  { rw [sign'_neg xneg, sign'_pos ypos, sign'_neg (mul_neg_of_neg_of_pos xneg ypos), mone_mul_one] },
  { rw [sign'_pos xpos, sign'_neg yneg, sign'_neg (linarith.mul_neg yneg xpos), one_mul_mone] },
  { rw [sign'_pos xpos, sign'_pos ypos, sign'_pos (mul_pos xpos ypos), one_mul_one] },
end

@[pm_one_simp, simp] lemma pm_one_sign'_mul {x y : ℚ} :
pm_one (sign' x * sign' y) = pm_one (sign' x) * pm_one (sign' y) :=
begin
  cases sign' x; cases sign' y; simp,
end

end pm

@[simp]
lemma add_neg_self' (q : ℚ): q⁻¹ + (-1) / q = 0 :=
begin
  field_simp,
end

@[simp]
lemma add_neg_self'' (q : ℚ) : (-1) / q + q⁻¹ = 0 :=
begin
  field_simp,
end

@[simp]
lemma half_add_half : (2:ℚ)⁻¹ + (2:ℚ)⁻¹ = 1 :=
begin
  ring,
end

lemma neg_one_div (q : ℚ) : ((-1) / q) = -q⁻¹ := by ring 

lemma one_ne_neg_one : (1 : ℚ) ≠ (-1 : ℚ) := by dec_trivial

lemma neg_one_ne_one : ¬(-1 : ℚ) = (1 : ℚ) := by dec_trivial

lemma neq_one_pow_add' (a b : ℕ) : (-1 : ℚ) ^ a * (-1) ^ b = (-1) ^ (a + b) :=
begin
  exact tactic.ring.pow_add_rev (-1) a b,
end

lemma neg_sq' (a : ℕ) : (-1 : ℚ) ^ a * (-1) ^ a = 1 :=
begin
  rw [← sq, ← pow_mul, mul_comm],
  simp only [pow_mul, sq, one_pow, mul_one, neg_neg, mul_neg],
end