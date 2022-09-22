import matrix_simp
import random_stuff

namespace HW_matrix
open matrix

lemma one_def : (1 : matrix (fin 4) (fin 4) ℚ) 
= ![![1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, 1, 0],
  ![0, 0, 0, 1]] :=
begin
  ext i j : 2,
  fin_cases i; fin_cases j; refl,
end

@[derive decidable_rel]
def lt : GL (fin 4) ℚ → GL (fin 4) ℚ → Prop :=
λ g₁ g₂, (g₁ 3 0 < g₂ 3 0) ∨ ((g₁ 3 0 = g₂ 3 0) ∧ (g₁ 3 1 < g₂ 3 1)) ∨ 
  ((g₁ 3 0 = g₂ 3 0) ∧ (g₁ 3 1 = g₂ 3 1) ∧ (g₁ 3 2 < g₂ 3 2))

instance : has_lt (GL (fin 4) ℚ) := ⟨lt⟩

def le (g₁ g₂ : GL (fin 4) ℚ) : Prop := g₁ < g₂ ∨ g₁ = g₂

instance : has_le (GL (fin 4) ℚ) := ⟨le⟩

lemma le_refl : ∀ (g : GL (fin 4) ℚ), g ≤ g :=
begin
  intro g,
  unfold has_le.le le,
  right,
  refl
end

/- lemma le_trans : ∀ (a b c : GL (fin 4) ℚ), a ≤ b → b ≤ c → a ≤ c :=
begin
  unfold has_le.le le,
  rintros a b c ⟨hab, hab2⟩ ⟨hbc, hbc2⟩,
  
end -/

/- instance : partial_order (GL (fin 4) ℚ) :=
{ le := (≤), 
  lt := (<),
  le_refl := le_refl,
  le_trans := _,
  lt_iff_le_not_le := _,
  le_antisymm := _ } -/

instance : decidable_eq (GL (fin 4) ℚ) := units.decidable_eq

def a: GL (fin 4) ℚ :=
{ val :=![![1, 0, 0, 0], 
  ![0, -1, 0, 0],
  ![0, 0, -1, 0],
  ![1/2, 0, 0, 1]],
  inv := ![![1, 0, 0, 0], 
  ![0, -1, 0, 0],
  ![0, 0, -1, 0],
  ![-1/2, 0, 0, 1]],
  val_inv := by field_simp[one_def],
  inv_val := by field_simp[one_def] }

def b: GL (fin 4) ℚ :=
{ val :=![![-1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, -1, 0], 
  ![0, 1/2, 1/2, 1]],
  inv := ![![-1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, -1, 0], 
  ![0, -1/2, 1/2, 1]],
  val_inv := by field_simp[one_def],
  inv_val := by field_simp[one_def] }

def x : GL (fin 4) ℚ := a ^ 2

def y : GL (fin 4) ℚ := b ^ 2

def z : GL (fin 4) ℚ := (a * b) ^ 2

lemma rel_1 : a⁻¹ * b ^ 2 * a * b ^ 2 = 1 :=
begin
  ext1,
  norm_num[a, b, sq, one_def]
end

lemma rel_2 : b⁻¹ * a ^ 2 * b * a ^ 2 = 1 :=
begin
  ext1,
  norm_num[a, b, sq, one_def]
end

lemma a_two_pow (n : ℤ) : (a ^ 2) ^ n 
= { val :=![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![n, 0, 0 , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0],
  ![-n, 0 , 0 , 1]],
  val_inv := by field_simp[HW_matrix.one_def],
  inv_val := by field_simp[HW_matrix.one_def] } := 
begin
  cases n,
  { induction n with i hi,
    { simp only [int.cast_zero, nat.nat_zero_eq_zero, int.coe_nat_zero, zpow_zero, int.of_nat_eq_coe, neg_zero],
      ext1,
      simp [one_def] },
    { have h : (a ^ 2) ^ int.of_nat i.succ = a ^ 2 * ((a ^ 2) ^ int.of_nat i) := rfl,
      rw [h, hi],
      unfold a,
      rw [sq, GL_mul_apply, GL_mul_apply],
      simp [add_comm (1:ℚ) i, add_comm (-1:ℚ) (-i)] }},
  { induction n with i hi,
    { unfold a,
      rw [sq, GL_mul_apply],
      simp only [mul_eq_mul, cons_mul, vec_mul_cons, head_cons, smul_cons, algebra.id.smul_eq_mul,
        mul_one, mul_zero, tail_cons, zero_mul, empty_vec_mul, add_zero, empty_add_empty,
        cons_add_cons, zero_add, one_mul, empty_mul, eq_self_iff_true, neg_mul, add_left_neg,
        neg_neg, add_halves', int.cast_neg_succ_of_nat, nat.cast_zero, zpow_neg_succ_of_nat,
        pow_one, units.inv_mk, and_self]},
    { have h : (a ^ 2) ^ -[1+ i.succ] = (a ^ 2) ^ (-1 : ℤ) * ((a ^ 2) ^ -[1+ i]),
      { rw ← zpow_add (a ^ 2),
        have h2 : -1 + -[1+ i] = -[1+ i.succ],
        { rw [add_comm, int.add_neg_one, int.neg_succ_sub_one] },
          simp [h2] },
      rw [h, hi],
      unfold a,
      rw [sq, GL_mul_apply, GL_mul_apply],
      simp }}
end

lemma b_two_pow (n : ℤ) : (b^2)^n 
= { val :=![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, n, 0 , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, -n , 0 , 1]],
  val_inv := by field_simp[HW_matrix.one_def],
  inv_val := by field_simp[HW_matrix.one_def] } :=
begin
  cases n,
  { induction n with i hi,
    { simp only [int.cast_zero, nat.nat_zero_eq_zero, int.coe_nat_zero, zpow_zero, int.of_nat_eq_coe, neg_zero],
      ext1,
      simp [one_def] },
    { have h : (b ^ 2) ^ int.of_nat i.succ = b ^ 2 * ((b ^ 2) ^ int.of_nat i) := rfl,
      rw [h, hi],
      unfold b,
      rw [sq, GL_mul_apply, GL_mul_apply],
      simp [add_comm (1:ℚ) i, add_comm (-1:ℚ) (-i)] }},
  { induction n with i hi,
    { unfold b,
      rw [sq, GL_mul_apply],
      simp },
    { have h : (b ^ 2) ^ -[1+ i.succ] = (b^2)^(-1:ℤ) * ((b ^ 2) ^ -[1+ i]),
      { rw ← zpow_add (b^2),
        have h2 : -1 + -[1+ i] = -[1+ i.succ],
        { rw [add_comm, int.add_neg_one, int.neg_succ_sub_one] },
        simp[h2] },
      rw [h, hi],
      unfold b,
      rw [sq, GL_mul_apply, GL_mul_apply],
      simp }}
end

lemma ab_two_pow (n : ℤ) : ((a * b)^2)^n = 
{ val :=![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0, n , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0 , -n , 1]],
  val_inv := by simp[HW_matrix.one_def],
  inv_val := by simp[HW_matrix.one_def] } :=
begin
  cases n,
  { induction n with i hi,
    { simp only [int.cast_zero, nat.nat_zero_eq_zero, int.coe_nat_zero, zpow_zero, int.of_nat_eq_coe, neg_zero],
      ext1,
      simp [one_def] },
    { have h : ((a * b) ^ 2) ^ int.of_nat i.succ = (a * b)^2 * (((a * b) ^ 2) ^ int.of_nat i) := rfl,
      rw [h, hi],
      unfold a b,
      rw [sq, GL_mul_apply, GL_mul_apply],
      simp [add_comm (1:ℚ) i, add_comm (-1:ℚ) (-i), ← two_mul (-2⁻¹ : ℚ)] }},
  { induction n with i hi,
    { unfold a b,
      rw [sq, GL_mul_apply],
      simp [← two_mul (-2⁻¹ : ℚ)] },
    { have h : ((a * b) ^ 2) ^ -[1+ i.succ] = ((a * b) ^ 2) ^ (-1:ℤ) * (((a * b) ^ 2) ^ -[1+ i]),
      { rw ← zpow_add ((a * b) ^ 2),
        have h2 : -1 + -[1+ i] = -[1+ i.succ],
        { rw [add_comm, int.add_neg_one, int.neg_succ_sub_one] },
        simp[h2] },
      rw h,
      rw hi,
      unfold a b,
      rw [sq, GL_mul_apply, GL_mul_apply],
      simp [← two_mul (-2⁻¹ : ℚ)] }}
end

lemma x_pow (n : ℤ) : x ^ n
= { val := ![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![n, 0, 0 , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![-n, 0 , 0 , 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] } :=
begin
  unfold x,
  exact HW_matrix.a_two_pow n,
end

lemma y_pow (n : ℤ) : y ^ n 
= { val :=![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, n, 0 , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, -n , 0 , 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] } :=
begin
  unfold y,
  exact HW_matrix.b_two_pow n,
end

lemma z_pow (n : ℤ) : z ^ n
= { val :=![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0, n , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0 , -n , 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] } :=
begin
  unfold z,
  exact HW_matrix.ab_two_pow n,
end

lemma xyz_pow (nx ny nz : ℤ) : x ^ nx * y ^ ny * z ^ nz
= { val :=![![1, 0, 0, 0],
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![nx, ny, nz , 1]],
  inv :=![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![-nx, -ny , -nz , 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] } := 
begin
  rw [x_pow, y_pow, z_pow, GL_mul_apply, GL_mul_apply],
  simp,
end

def pre_from_word : (generator × bool) → GL (fin 4) ℚ
| (generator.a, tt) := a
| (generator.b, tt) := b
| (generator.a, ff) := a⁻¹
| (generator.b, ff) := b⁻¹

@[simp] lemma pre_from_word_a_tt : pre_from_word (generator.a, tt) = a := rfl

@[simp] lemma pre_from_word_b_tt : pre_from_word (generator.b, tt) = b := rfl

@[simp] lemma pre_from_word_a_ff : pre_from_word (generator.a, ff) = a⁻¹ := rfl

@[simp] lemma pre_from_word_b_ff : pre_from_word (generator.b, ff) = b⁻¹ := rfl

def from_word : list (generator × bool) → GL (fin 4) ℚ := 
begin
  intro l,
  induction l,
  { exact 1 },
  { exact pre_from_word l_hd * l_ih }
end

@[simp] lemma from_word_nil : from_word list.nil = 1 := rfl

@[simp] lemma from_word_cons {l_hd : (generator × bool)} {l_tl : list (generator × bool)} :
from_word (l_hd :: l_tl) = pre_from_word l_hd * from_word l_tl := rfl

@[simp] lemma from_word_mul (lx ly : list (generator × bool)) :
from_word (lx ++ ly) = from_word lx * from_word ly :=
begin
  induction lx,
  { simp },
  { simp [lx_ih, from_word_cons, mul_assoc] }
end

def pre_from_word_reverse_bool : (generator × bool) → (generator × bool)
| (g, tt) := (g, ff)
| (g, ff) := (g, tt)

@[simp] lemma pre_from_word_reverse_tt {g : generator} :
pre_from_word_reverse_bool (g, tt) = (g, ff) := rfl

@[simp] lemma pre_from_word_reverse_ff {g : generator} :
pre_from_word_reverse_bool (g, ff) = (g, tt) := rfl

def from_word_reverse_bool (l: list (generator × bool)) : list (generator × bool) :=
begin
  induction l,
  { exact list.nil },
  { exact pre_from_word_reverse_bool l_hd :: l_ih }
end

@[simp] lemma from_word_reverse_bool_hd_tl {l_hd : (generator × bool)} {l_tl : list (generator × bool)} :
from_word_reverse_bool (l_hd :: l_tl) = pre_from_word_reverse_bool l_hd :: from_word_reverse_bool l_tl
:= rfl

@[simp] lemma from_word_reverse_nil : from_word_reverse_bool list.nil = list.nil := rfl

@[simp] lemma from_word_inv (l: list (generator × bool)) :
from_word (list.reverse (from_word_reverse_bool l)) = (from_word l)⁻¹ :=
begin
  induction l,
  { simp },
  { simp [from_word_cons, l_ih],
    cases l_hd with l_hd_gen l_hd_b,
    cases l_hd_gen; cases l_hd_b; simp }
end

end HW_matrix