import HW_group
import algebra.group.units

namespace torsion_free

open HW_group

--pm_one is ±1 

def HW_element (α β γ : ℚ) (e₁ e₂ e₃ : pm) : GL (fin 4) ℚ := 
{ val :=![![pm_one e₁, 0, 0, 0], 
  ![0, pm_one e₂, 0, 0], 
  ![0, 0, pm_one e₃, 0],
  ![α, β, γ, 1]],
  inv :=![![pm_one e₁, 0, 0, 0], 
  ![0, pm_one e₂, 0, 0], 
  ![0, 0, pm_one e₃, 0], 
  ![-pm_one e₁ * α, -pm_one e₂ * β, -pm_one e₃ * γ, 1]],
  val_inv := by field_simp [HW_matrix.one_def, mul_comm],
  inv_val := by field_simp [HW_matrix.one_def, mul_left_comm _ α,
              mul_assoc, mul_left_comm _ β, mul_left_comm _ γ] }

lemma pre_formX {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) : ∃(α β γ : ℚ) (e₁ e₂ : pm), 
g = HW_element α β γ e₁ e₂ (e₁ * e₂) := 
begin
  apply subgroup.closure_induction hg,
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      use [1/2, 0, 0, pm.one, pm.mone],
      dsimp only [HW_matrix.a, HW_element],
      apply HW_GL_ext,
      simp only [pm.one_mul, eq_self_iff_true, pm.pm_one_mone, pm.pm_one_one, and_self] },
    { rw set.mem_singleton_iff at hb,
      rw hb,
      use [0, 1/2, 1/2, pm.mone, pm.one],
      unfold HW_matrix.b HW_element,
      apply HW_GL_ext,
      simp only [pm.mul_one, eq_self_iff_true, pm.pm_one_mone, pm.pm_one_one, and_self] }},
  { use [0, 0, 0, pm.one, pm.one],
    unfold HW_element,
    simp only [one_def, pm.one_mul, pm.pm_one_one, and_self, mul_zero] },
  { rintros x y ⟨αx, βx, γx, e₁x, e₂x, hx⟩ ⟨αy, βy, γy, e₁y, e₂y, hy⟩,
    use [αx * (pm_one e₁y) + αy, βx * (pm_one e₂y) + βy, γx * (pm_one (e₁y * e₂y)) + γy,
        e₁x * e₁y, e₂x * e₂y],
    rw [hx, hy],
    unfold HW_element,
    rw GL_mul_apply,
    dsimp only,
    simp only [neg_one_mul, add_zero, mul_one, one_mul,
      zero_mul, zero_add, pm.pm_one_mul, mul_zero],
    split; rw [matrix.mul_eq_mul, matrix_mul_apply, ← HW_matrix_ext_iff];
    cases e₁x;
    cases e₂x;
    cases e₁y;
    cases e₂y,
    repeat { simp only [one_mul, mul_one, add_left_inj, eq_self_iff_true, and_self, true_and,
      mul_neg, neg_one_mul, neg_neg, neg_inj, neg_add_rev,
      add_comm αy, add_comm βy, add_comm γy] with pm_one_simp } },
  { rintros x ⟨α, β, γ, e₁, e₂, hx⟩,
    use [-pm_one e₁ * α, -pm_one e₂ * β, -pm_one (e₁ * e₂) * γ, e₁, e₂],
    rw hx,
    unfold HW_element,
    rw [GL_inv, GL_ext_iff] } 
end

@[simp] lemma HW_group_00 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
g 0 0 = 1 ∨ g 0 0 = -1 :=
begin
  obtain ⟨α, β, γ, e₁, e₂, fg⟩ := pre_formX hg,
  rw fg,
  unfold HW_element,
  simp only with HW_matrix_simp,
  cases e₁,
  { simp only [true_or, eq_self_iff_true, pm.pm_one_one] },
  { simp only [eq_self_iff_true, pm.pm_one_mone, or_true] }
end

@[simp] lemma HW_group_00''' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
¬g 0 0 = 1 ↔ g 0 0 = -1 :=
begin
  cases HW_group_00 hg;
  norm_num [h]
end

@[simp] lemma HW_group_11 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
g 1 1 = 1 ∨ g 1 1 = -1 :=
begin
  obtain ⟨α, β, γ, e₁, e₂, fg⟩ := pre_formX hg,
  rw fg,
  unfold HW_element,
  simp only with HW_matrix_simp,
  cases e₂,
  { simp only [true_or, eq_self_iff_true, pm.pm_one_one] },
  { simp only [eq_self_iff_true, pm.pm_one_mone, or_true] }
end

@[simp] lemma HW_group_11''' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
¬g 1 1 = 1 ↔ g 1 1 = -1 :=
begin
  cases HW_group_11 hg;
  norm_num [h]
end

@[simp] lemma HW_group_22 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
g 2 2 = 1 ∨ g 2 2 = -1 :=
begin
  obtain ⟨α, β, γ, e₁, e₂, fg⟩ := pre_formX hg,
  rw fg,
  unfold HW_element,
  simp only with HW_matrix_simp,
  cases e₁;
  cases e₂,
  { simp only [pm.one_mul, true_or, eq_self_iff_true, pm.pm_one_one] },
  { simp only [pm.one_mul, eq_self_iff_true, pm.pm_one_mone, or_true] },
  { simp only [pm.mul_one, eq_self_iff_true, pm.pm_one_mone, or_true] },
  { simp only [pm.mone_mul_mone, true_or, eq_self_iff_true, pm.pm_one_one] }
end

@[simp] lemma HW_group_00' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
pm_one (pm.sign' (g 0 0)) = g 0 0 :=
by cases HW_group_00 hg; simp[h]

@[simp] lemma HW_group_11' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
pm_one (pm.sign' (g 1 1)) = g 1 1 :=
by cases HW_group_11 hg; simp[h]

@[simp] lemma HW_group_22' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
pm_one (pm.sign' (g 2 2)) = g 2 2 :=
by cases HW_group_22 hg; simp[h]

lemma HW_group_00'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g : matrix (fin 4) (fin 4) ℚ) 0 0 ≠ 0 :=
by cases HW_group_00 hg; simp[h]

lemma HW_group_11'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g : matrix (fin 4) (fin 4) ℚ) 1 1 ≠ 0 :=
by cases HW_group_11 hg; simp[h]

lemma HW_group_22'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g : matrix (fin 4) (fin 4) ℚ) 2 2 ≠ 0 :=
by cases HW_group_22 hg; simp[h]

lemma HW_element_mul (αx βx γx : ℚ) (e₁x e₂x e₃x : pm) (αy βy γy : ℚ) (e₁y e₂y e₃y : pm) :
HW_element αx βx γx e₁x e₂x e₃x * HW_element αy βy γy e₁y e₂y e₃y
= HW_element (αx * pm_one e₁y + αy) (βx * pm_one e₂y + βy) (γx * pm_one e₃y + γy)
  (e₁x * e₁y) (e₂x * e₂y) (e₃x * e₃y) := 
begin
  unfold HW_element,
  rw [GL_mul_apply, GL_ext_iff],
  simp only [add_zero, mul_one, one_mul, zero_mul, zero_add, matrix.mul_eq_mul, pm.pm_one_mul,
    mul_zero],
  rw [matrix_mul_apply, ← HW_matrix_ext_iff],
  cases e₁y;
  cases e₂y;
  cases e₃y;
  simp only [one_mul, mul_one, true_and, eq_self_iff_true,
    true_and, add_left_inj, mul_neg, neg_inj] with pm_one_simp
end

def formX : GL (fin 4) ℚ → GL (fin 4) ℚ :=
λ g, (HW_element (g 3 0) (g 3 1) (g 3 2)
     (pm.sign' (g 0 0)) (pm.sign' (g 1 1)) (pm.sign' (g 0 0) * pm.sign' (g 1 1)))

lemma HW_group_has_formX {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) : 
formX g = g :=
begin
  symmetry,
  suffices : (g ∈ HW_group) ∧ g = formX g,
  {exact this.right},
  unfold formX,
  apply subgroup.closure_induction'' hg,
  { unfold HW_element,
    intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      unfold HW_matrix.a,
      simp only with HW_matrix_simp pm_one_simp,
      simp only [true_and, one_div, one_mul, eq_self_iff_true, 
        neg_neg, neg_one_div, neg_one_mul] },
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true]},
      unfold HW_matrix.b,
      simp only [one_div, mul_one, zero_div, eq_self_iff_true, and_self, neg_neg, mul_zero, one_mul,
        neg_one_div 2, neg_one_mul] with HW_matrix_simp pm_one_simp }},
  { unfold HW_element,
    intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      rw GL_inv,
      unfold HW_matrix.a,
      simp only with pm_one_simp HW_matrix_simp,
      split; apply HW_matrix_ext,
      { simp only [eq_self_iff_true, and_self] },
      { simp only [true_and, one_div, one_mul, and_true, eq_self_iff_true, 
          neg_neg, neg_one_div 2, mul_zero, neg_one_mul] }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      rw GL_inv,
      unfold HW_matrix.b,
      simp only with HW_matrix_simp pm_one_simp,
      split; apply HW_matrix_ext,
      { simp only [eq_self_iff_true, and_self] },
      { simp only [neg_one_mul, true_and, one_div, one_mul, and_true, eq_self_iff_true,
          neg_neg, neg_one_div 2] }}},
  { unfold HW_element,
    use HW_group.one_mem',
    rw HW_group.one_def,
    apply HW_GL_ext,
    simp only with HW_matrix_simp,
    simp only [pm.one_mul, eq_self_iff_true, pm.pm_one_one, and_self, pm.sign'_pos, zero_lt_one] },
  { rintros x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩,
    use HW_group.mul_mem' hx1 hy1,
    conv_lhs { rw [hx2, hy2]},
    rw HW_element_mul,
    unfold HW_element,
    apply HW_GL_ext,
    have h00 := pm.sign'_mul (HW_group_00'' hx1) (HW_group_00'' hy1),
    have h11 := pm.sign'_mul (HW_group_11'' hx1) (HW_group_11'' hy1),
    have hx00 := HW_group_00' hx1,
    have hy00 := HW_group_00' hy1, 
    have hx11 := HW_group_11' hx1,
    have hy11 := HW_group_11' hy1,
    simp only [matrix.general_linear_group.coe_fn_eq_coe] at h00 h11 hx00 hy00 hx11 hy11,
    simp only [h00, h11, hx00, hy00, hx11, hy11] 
      with HW_matrix_simp pm_one_simp,
    have xy : x * y = x * y := rfl,
    conv_rhs at xy { rw [hx2, hy2] },
    clear hx2 hy2 h00 h11 hx00 hy00 hx11 hy11,
    unfold HW_element at xy,
    conv_rhs at xy { rw GL_mul_apply },
    rw GL_ext_iff at xy,
    simp only [add_zero, mul_one, one_mul, zero_mul, units.val_eq_coe, pm.pm_one_sign'_mul,
      zero_add, matrix.mul_eq_mul, mul_zero] at xy,
    conv_rhs at xy { rw matrix_mul_apply },
    simp only [pm.pm_one_sign'_mul, xy] with HW_matrix_simp,
    clear xy,
    cases HW_group_00 hx1 with hx00 hx00;
    cases HW_group_11 hx1 with hx11 hx11;
    cases HW_group_00 hy1 with hy00 hy00;
    cases HW_group_11 hy1 with hy11 hy11;
    rw matrix.general_linear_group.coe_fn_eq_coe at hx00 hy00 hx11 hy11;
    simp only [hx00, hy00, hx11, hy11, mul_one, eq_self_iff_true, pm.pm_one_one, and_self, 
      pm.sign'_pos, pm.sign'_neg, zero_lt_one, right.neg_neg_iff, mul_neg,
      pm.pm_one_mone, and_self, neg_neg] }
end

lemma HW_group_has_formX' {g : HW_group}: 
formX g = g :=
begin
  apply HW_group_has_formX,
  simp,
end

lemma formX_unique (x : GL (fin 4) ℚ) (hx : x ∈ HW_group) (y : GL (fin 4) ℚ) (hy : y ∈ HW_group) :
formX x = formX y → x = y :=
begin
  rw HW_group_has_formX hx,
  rw HW_group_has_formX hy,
  intro h,
  exact h,
end

@[simp]
lemma formX_element {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) (i j : ℕ) :
formX g i j = g i j := by rw HW_group_has_formX hg

@[simp]
lemma formX_element' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) (i j : ℕ) :
(formX g : matrix (fin 4) (fin 4) ℚ) i j = (g : matrix (fin 4) (fin 4) ℚ) i j
:= by rw HW_group_has_formX hg

@[simp]
lemma formX_element'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) (i j : ℕ) :
(↑(formX g) : matrix (fin 4) (fin 4) ℚ) i j = (↑g : matrix (fin 4) (fin 4) ℚ) i j 
:= by rw HW_group_has_formX hg

lemma square_diag_one_00 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g^2) 0 0 = 1 :=
begin
  rw sq,
  rw ← HW_group_has_formX hg,
  unfold formX,
  unfold HW_element,
  simp with HW_matrix_simp
end

lemma square_diag_one_11 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g^2) 1 1 = 1 :=
begin
  rw sq,
  rw ← HW_group_has_formX hg,
  unfold formX,
  unfold HW_element,
  simp with HW_matrix_simp
end

lemma square_diag_one_22 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g^2) 2 2 = 1 :=
begin
  rw sq,
  rw ← HW_group_has_formX hg,
  unfold formX,
  unfold HW_element,
  simp only [pm.pm_one_sign'_mul] with HW_matrix_simp,
  cases HW_group_00 hg;
  simp at h;
  simp[h]
end

lemma square_diag_one {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(g^2) 0 0 = 1 ∧ (g^2) 1 1 = 1 ∧ (g^2) 2 2 = 1 :=
begin
  split,
  exact square_diag_one_00 hg,
  split,
  exact square_diag_one_11 hg,
  exact square_diag_one_22 hg
end

lemma diag_one_pow {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) (n : ℕ) :
(g 0 0 = 1 ∧ g 1 1 = 1 ∧ g 2 2 = 1) → 
g ^ n = HW_element (n * (g 3 0)) (n * (g 3 1)) (n * (g 3 2)) pm.one pm.one pm.one :=
begin
  rintro ⟨h1, h2, h3⟩,
  unfold HW_element,
  simp,
  induction n with n hn,
  { simp only [one_def, nat.cast_zero, zero_mul, and_self, pow_zero, neg_zero] },
  { have h : g^n.succ = (formX g) * g^n,
    { rw HW_group_has_formX hg, 
      rw pow_succ },
    rw h,
    simp,
    unfold formX,
    unfold HW_element,
    simp[h1, h2, h3, hn],
    rw GL_mul_apply,
    simp,
    split,
    { apply HW_matrix_ext,
      simp [add_mul, add_comm] },
    { apply HW_matrix_ext,
      simp [add_mul, add_comm] }}
end

lemma HW_group_22_eq_00_mul_11 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) : 
g 2 2 = g 0 0 * g 1 1 :=
begin
  rw ← HW_group_has_formX hg,
  unfold formX HW_element,
  simp only with HW_matrix_simp,
  simp only [pm.pm_one_sign'_mul],
end

lemma HW_mul_30 {x y : GL (fin 4) ℚ} (hx : x ∈ HW_group) (hy : y ∈ HW_group) :
(x * y) 3 0 = x 3 0 * y 0 0 + y 3 0 :=
begin
  conv_lhs { rw ← HW_group_has_formX hx, 
             rw ← HW_group_has_formX hy },
  unfold formX,
  rw HW_element_mul,
  unfold HW_element,
  simp only with HW_matrix_simp,
  cases HW_group_00 hy;
  simp at h;
  simp [h],
end

lemma HW_mul_31 {x y : GL (fin 4) ℚ} (hx : x ∈ HW_group) (hy : y ∈ HW_group) :
(x * y) 3 1 = x 3 1 * y 1 1 + y 3 1 :=
begin
  conv_lhs { rw ← HW_group_has_formX hx, 
             rw ← HW_group_has_formX hy },
  unfold formX,
  rw HW_element_mul,
  unfold HW_element,
  simp only with HW_matrix_simp,
  cases HW_group_11 hy;
  simp at h;
  simp [h],
end

lemma HW_mul_32 {x y : GL (fin 4) ℚ} (hx : x ∈ HW_group) (hy : y ∈ HW_group) :
(x * y) 3 2 = x 3 2 * y 2 2 + y 3 2 :=
begin
  rw HW_group_22_eq_00_mul_11 hy,
  conv_lhs { rw ← HW_group_has_formX hx, 
             rw ← HW_group_has_formX hy },
  unfold formX,
  rw HW_element_mul,
  unfold HW_element,
  simp only with HW_matrix_simp,
  cases HW_group_00 hy with h00 h00;
  cases HW_group_11 hy with h11 h11;
  simp at h00 h11;
  simp [h00, h11]
end

lemma HW_mul_11 {x y : GL (fin 4) ℚ} (hx : x ∈ HW_group) (hy : y ∈ HW_group) :
(x * y) 1 1 = x 1 1 * y 1 1 :=
begin
  conv_lhs { rw ← HW_group_has_formX hx, 
             rw ← HW_group_has_formX hy },
  unfold formX,
  rw HW_element_mul,
  unfold HW_element,
  simp only with HW_matrix_simp,
  simp,
  cases HW_group_11 hy with hy2 hy2;
  cases HW_group_11 hx with hx2 hx2;
  simp at hy2 hx2;
  simp [hy2, hx2]
end

lemma HW_mul_00 {x y : GL (fin 4) ℚ} (hx : x ∈ HW_group) (hy : y ∈ HW_group) :
(x * y) 0 0 = x 0 0 * y 0 0 :=
begin
  conv_lhs { rw ← HW_group_has_formX hx, 
             rw ← HW_group_has_formX hy },
  unfold formX,
  rw HW_element_mul,
  unfold HW_element,
  simp only with HW_matrix_simp,
  simp,
  cases HW_group_00 hy with hy2 hy2;
  cases HW_group_00 hx with hx2 hx2;
  simp at hy2 hx2;
  simp [hy2, hx2]
end

lemma HW_mul_22 {x y : GL (fin 4) ℚ} (hx : x ∈ HW_group) (hy : y ∈ HW_group) :
(x * y) 2 2 = x 2 2 * y 2 2 :=
begin
  rw [HW_group_22_eq_00_mul_11 hx, HW_group_22_eq_00_mul_11 hy],
  conv_lhs { rw [← HW_group_has_formX hx, ← HW_group_has_formX hy] },
  unfold formX,
  rw HW_element_mul,
  unfold HW_element,
  simp only with HW_matrix_simp,
  simp only [pm.pm_one_mul],
  cases HW_group_00 hx with hx00 hx00;
  cases HW_group_11 hx with hx11 hx11;
  cases HW_group_00 hy with hy00 hy00;
  cases HW_group_11 hy with hy11 hy11;
  simp only [matrix.general_linear_group.coe_fn_eq_coe] at hx00 hx11 hy11 hy00;
  simp [hx00, hx11, hy11, hy00]
end

lemma two_inv_denom : (2 : ℚ)⁻¹.denom = 2 :=
begin
  have h20 : (0 : ℤ) < 2 := dec_trivial,
  have h := rat.inv_coe_int_denom h20,
  simp only [int.cast_bit0, int.cast_one] at h,
  apply int.coe_nat_inj h,  
end

lemma int_ne_half (z : ℤ) : (z : ℚ) ≠ 2⁻¹ :=
begin
  rw ne.def,
  rw rat.ext_iff,
  rw not_and,
  intro h,
  simp [two_inv_denom],
end

lemma half_ne_int (z : ℤ) : 2⁻¹ ≠ (z : ℚ) :=
begin
  rw ne.def,
  rw rat.ext_iff,
  rw not_and,
  intro h,
  simp [two_inv_denom],
end

lemma int_ne_int_add_half (z₁ z₂ : ℤ) : (z₁ : ℚ) ≠ (z₂ : ℚ) + 2⁻¹ := 
begin
  suffices : (z₁ : ℚ) - (z₂ : ℚ) ≠ 2⁻¹,
  { contrapose this,
    simp only [not_not] at *,
    rw this,
    simp only [add_tsub_cancel_left] },
  suffices : (↑(z₁ - z₂) : ℚ) ≠ 2⁻¹,
  { simpa using this },
  apply int_ne_half
end

lemma int_ne_int_add_half' (z₁ z₂ : ℤ) :  (z₂ : ℚ) + 2⁻¹ ≠ (z₁ : ℚ) := 
begin
  suffices : (z₁ : ℚ) - (z₂ : ℚ) ≠ 2⁻¹,
  { contrapose this,
    simp only [not_not] at *,
    rw this.symm,
    simp only [add_tsub_cancel_left] },
  suffices : (↑(z₁ - z₂) : ℚ) ≠ 2⁻¹,
  { simpa using this },
  apply int_ne_half
end

lemma int_ne_int_add_half'' (z1 z2 z3 : ℤ) : 
(z1 : ℚ) + (z2 : ℚ) ≠ (z3 : ℚ) + 2⁻¹ := 
begin
  suffices : (↑(z1 + z2) : ℚ) ≠ (z3 : ℚ) + 2⁻¹,
  { simpa using this },
  apply int_ne_int_add_half
end

lemma add_halfes (q : ℚ) : q + 2⁻¹ + 2⁻¹ = q + 1 := by rw [add_assoc, half_add_half]

lemma int_cast_one_rat (q : ℚ) : q + (1 : ℚ) = q + ↑(1 : ℤ) := by rw int.cast_one.symm

lemma int_cast_neg_one_rat (q : ℚ) : q + (-1 : ℚ) = q + ↑(-1 : ℤ) := 
by rw [int.cast_neg, int.cast_one]

lemma int_cast_one_rat' (q : ℚ) : (1 : ℚ) + q = ↑(1 : ℤ) + q := by rw int.cast_one.symm

lemma int_cast_neg_one_rat' (q : ℚ) : (-1 : ℚ) + q = ↑(-1 : ℤ) + q := 
by rw [int.cast_neg, int.cast_one]

lemma two_inv : (-2⁻¹ : ℚ) = 2⁻¹ - 1 :=
begin
  suffices : (0 : ℚ) = 2⁻¹ + 2⁻¹ - 1,
  { rw [← add_zero (-2⁻¹ : ℚ), this, ← add_sub, ← add_assoc, add_left_neg, zero_add] },
  simp only [half_add_half, sub_self]
end

lemma HW_group_30_help (x y : GL (fin 4) ℚ) : 
x ∈ HW_group ∧ ((∃ (z : ℤ), x 3 0 = z) ↔ x 1 1 = 1) ∧ 
((∃ (z : ℤ), x 3 0 = z + 1 / 2) ↔ x 1 1 = -1) → y ∈ HW_group ∧ 
((∃ (z : ℤ), y 3 0 = ↑z) ↔ y 1 1 = 1) ∧ ((∃ (z : ℤ), y 3 0 = ↑z + 1 / 2) ↔ 
y 1 1 = -1) → x * y ∈ HW_group ∧ ((∃ (z : ℤ), (x * y) 3 0 = ↑z) ↔ (x * y) 1 1 = 1) ∧ 
((∃ (z : ℤ), (x * y) 3 0 = ↑z + 1 / 2) ↔ (x * y) 1 1 = -1) :=
begin
  rintros ⟨hx, hx2, hx3⟩ ⟨hy, hy2, hy3⟩,
    use HW_group.mul_mem' hx hy,
    have hxy30 := HW_mul_30 hx hy, 
    have hxy31 := HW_mul_31 hx hy,
    have hxy00 := HW_mul_00 hx hy, 
    have hxy11 := HW_mul_11 hx hy,
    simp only [one_div, matrix.general_linear_group.coe_mul, 
      matrix.general_linear_group.coe_fn_eq_coe] at *,
    simp only [hxy30, hxy31, hxy00, hxy11],
    clear hxy30 hxy31 hxy00 hxy11,
    have neg_one_mul_neg_one : (-1 : ℚ) * (-1 : ℚ) = (1 : ℚ) :=
    by simp only [mul_one, mul_neg, neg_neg],
    cases HW_group_11 hx with hx11 hx11;
    cases HW_group_11 hy with hy11 hy11;
    cases HW_group_00 hy with hy00 hy00;
    split;
    split;
    simp only [matrix.general_linear_group.coe_fn_eq_coe] at hx11 hy11 hy00;
    simp only [implies_true_iff, iff_true, hx11, hy11, forall_exists_index, eq_self_iff_true,
      hx11, hy11, mul_one, one_mul, eq_self_iff_true, forall_true_left,
      one_ne_neg_one, one_ne_neg_one.symm, forall_false_left, 
      mul_neg, neg_neg, imp_false, not_exists] at ⊢ hx2 hx3 hy2 hy3;
    try {cases hx2 with zx2 hx2};
    try {cases hx3 with zx3 hx3};
    try {cases hy2 with zy2 hy2};
    try {cases hy3 with zy3 hy3};
    simp only [hy00, mul_neg_one, mul_one, hx2, hx3, hy2, hy3];
    simp only [push_neg.not_eq, add_comm (2⁻¹ : ℚ),
      ← int.cast_add, int.cast_inj, exists_eq', ← int.cast_neg, add_left_inj,
      int_ne_int_add_half, int_ne_int_add_half', not_false_iff, forall_const, neg_add, two_inv,
      ← add_assoc, add_right_comm _ (2⁻¹ : ℚ), sub_eq_add_neg, add_halfes,
      int_cast_one_rat, int_cast_neg_one_rat]
end

lemma HW_group_30 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
((∃ z : ℤ, g 3 0 = ↑z) ↔ g 1 1 = 1) 
∧ ((∃ z : ℤ, g 3 0 = ↑z + 1 / 2) ↔ g 1 1 = -1) :=
begin
  suffices : g ∈ HW_group 
  ∧ (((∃ z : ℤ, g 3 0 = ↑z) ↔ g 1 1 = 1) 
  ∧ ((∃ z : ℤ, g 3 0 = ↑z + 1 / 2) ↔ g 1 1 = -1)),
  {exact this.right},
  apply subgroup.closure_induction'' hg,
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      unfold HW_matrix.a,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_ne_neg_one.symm, half_ne_int, one_div, exists_false] },
      { simp only [int.cast_eq_zero, self_eq_add_left, eq_self_iff_true, exists_apply_eq_apply] }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      unfold HW_matrix.b,
      simp only with HW_matrix_simp,
      split,
      { simp only [eq_self_iff_true, iff_true],
        use 0,
        refl },
      { simp only [one_ne_neg_one, not_exists, one_div, iff_false],
        exact int_ne_int_add_half 0 }}},
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      rw GL_inv,
      unfold HW_matrix.a,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_ne_neg_one.symm, neg_one_div, two_inv, sub_eq_add_neg, int_cast_neg_one_rat, 
          not_exists, iff_false],
        simp only [add_comm (2⁻¹ : ℚ), int_ne_int_add_half', forall_const, not_false_iff] },
      { simp only [one_div, eq_self_iff_true, iff_true],
        use -1,
        simp only [neg_one_div, sub_eq_add_neg, add_comm, two_inv, int.cast_one, int.cast_neg] }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      rw GL_inv,
      unfold HW_matrix.b,
      simp only with HW_matrix_simp,
      split,
      { simp only [eq_self_iff_true, iff_true],
        use 0,
        refl },
      { simp only [one_ne_neg_one, not_exists, one_div, iff_false],
        exact int_ne_int_add_half 0 }}},
  { intros,
    use HW_group.one_mem',
    rw HW_group.one_def,
    simp only with HW_matrix_simp,
    split,
    { simp only [eq_self_iff_true, iff_true],
      use 0,
      refl },
    { simp [one_ne_neg_one],
      exact int_ne_int_add_half 0 }},
  { intros x y,
    exact HW_group_30_help x y }
end

lemma HW_group_30' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(∃ z : ℤ, g 3 0 = ↑z) ↔ g 1 1 = 1 := and.elim_left (HW_group_30 hg)

lemma HW_group_30'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(¬∃ z : ℤ, g 3 0 = ↑z) ↔ g 1 1 = -1 := 
begin
  rw and.elim_left (HW_group_30 hg),
  cases HW_group_11 hg;
  norm_num [h]
end

lemma HW_group_31_help (x y : GL (fin 4) ℚ) : 
x ∈ HW_group ∧ ((∃ (z : ℤ), x 3 1 = z) ↔ x 0 0 = 1) ∧ 
((∃ (z : ℤ), x 3 1 = z + 1 / 2) ↔ x 0 0 = -1) → y ∈ HW_group ∧ 
((∃ (z : ℤ), y 3 1 = ↑z) ↔ y 0 0 = 1) ∧ ((∃ (z : ℤ), y 3 1 = ↑z + 1 / 2) ↔ 
y 0 0 = -1) → x * y ∈ HW_group ∧ ((∃ (z : ℤ), (x * y) 3 1 = ↑z) ↔ (x * y) 0 0 = 1) ∧ 
((∃ (z : ℤ), (x * y) 3 1 = ↑z + 1 / 2) ↔ (x * y) 0 0 = -1) :=
begin
  rintros ⟨hx, hx2, hx3⟩ ⟨hy, hy2, hy3⟩,
    use HW_group.mul_mem' hx hy,
    have hxy30 := HW_mul_30 hx hy, 
    have hxy31 := HW_mul_31 hx hy,
    have hxy00 := HW_mul_00 hx hy, 
    have hxy11 := HW_mul_11 hx hy,
    simp only [one_div, matrix.general_linear_group.coe_mul, 
      matrix.general_linear_group.coe_fn_eq_coe] at *,
    simp only [hxy30, hxy31, hxy00, hxy11],
    clear hxy30 hxy31 hxy00 hxy11,
    have neg_one_mul_neg_one : (-1 : ℚ) * (-1 : ℚ) = (1 : ℚ) :=
    by simp only [mul_one, mul_neg, neg_neg],
    cases HW_group_00 hx with hx00 hx00;
    cases HW_group_11 hy with hy11 hy11;
    cases HW_group_00 hy with hy00 hy00;
    split;
    split;
    simp only [matrix.general_linear_group.coe_fn_eq_coe] at hx00 hy11 hy00;
    simp only [implies_true_iff, iff_true, forall_exists_index, eq_self_iff_true,
      hy00, hy11, hx00, mul_one, one_mul, eq_self_iff_true, forall_true_left,
      one_ne_neg_one, one_ne_neg_one.symm, forall_false_left, 
      mul_neg, neg_neg, imp_false, not_exists] at ⊢ hx2 hx3 hy2 hy3;    
    try {cases hx2 with zx2 hx2};
    try {cases hx3 with zx3 hx3};
    try {cases hy2 with zy2 hy2};
    try {cases hy3 with zy3 hy3};
    simp only [mul_neg_one, mul_one, hx2, hx3, hy2, hy3];
    simp only [push_neg.not_eq, add_comm (2⁻¹ : ℚ),
      ← int.cast_add, int.cast_inj, exists_eq', ← int.cast_neg, add_left_inj,
      int_ne_int_add_half, int_ne_int_add_half', not_false_iff, forall_const, neg_add, two_inv,
      ← add_assoc, add_right_comm _ (2⁻¹ : ℚ), sub_eq_add_neg, add_halfes,
      int_cast_one_rat, int_cast_neg_one_rat]
end

lemma HW_group_31 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(((∃ z : ℤ, g 3 1 = ↑z) ↔ g 0 0 = 1) 
∧ ((∃ z : ℤ, g 3 1 = ↑z + 1 / 2) ↔ g 0 0 = -1)) :=
begin
  suffices : g ∈ HW_group 
  ∧ (((∃ z : ℤ, g 3 1 = ↑z) ↔ g 0 0 = 1) 
  ∧ ((∃ z : ℤ, g 3 1 = ↑z + 1 / 2) ↔ g 0 0 = -1)),
  {exact this.right},
  apply subgroup.closure_induction'' hg,
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      unfold HW_matrix.a,
      simp only with HW_matrix_simp,
      split,
      { simp only [eq_self_iff_true, iff_true],
        use 0,
        refl },
      { simp only [not_exists, one_ne_neg_one, iff_false, one_div],
        exact int_ne_int_add_half 0 }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      unfold HW_matrix.b,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_ne_neg_one.symm, not_exists, one_div, iff_false],
        exact half_ne_int },
      { simp only [eq_self_iff_true, iff_true, one_div],
        use 0,
        simp only [int.cast_zero, zero_add] }}},
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      rw GL_inv,
      unfold HW_matrix.a,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_div, eq_self_iff_true, iff_true],
        use 0,
        refl },
      { simp only [one_ne_neg_one, not_exists, one_div, iff_false],
        exact int_ne_int_add_half 0 }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      rw GL_inv,
      unfold HW_matrix.b,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_ne_neg_one.symm, not_exists, one_div, iff_false, neg_one_div, two_inv,
          sub_eq_neg_add, int_cast_neg_one_rat'],
        intro z,
        exact int_ne_int_add_half' z (-1) },
      { simp only [eq_self_iff_true, iff_true, one_div, neg_one_div, two_inv],
        use -1,
        simp only [int.cast_one, int.cast_neg, add_comm (-1 : ℚ), sub_eq_add_neg] }}},
  { intros,
    use HW_group.one_mem',
    rw HW_group.one_def,
    simp only with HW_matrix_simp,
    split,
    { simp only [eq_self_iff_true, iff_true],
      use 0,
      refl },
    { simp [one_ne_neg_one],
      exact int_ne_int_add_half 0 }},
  { intros x y,
    exact HW_group_31_help x y }
end

lemma HW_group_31' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(∃ z : ℤ, g 3 1 = ↑z) ↔ g 0 0 = 1 := and.elim_left (HW_group_31 hg)

lemma HW_group_31'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(¬∃ z : ℤ, g 3 1 = ↑z) ↔ g 0 0 = -1 := 
begin
  rw and.elim_left (HW_group_31 hg),
  cases HW_group_00 hg;
  norm_num [h]
end

lemma HW_group_32_help (x y : GL (fin 4) ℚ) : 
x ∈ HW_group ∧ ((∃ (z : ℤ), x 3 2 = z) ↔ x 0 0 = 1) 
∧ ((∃ (z : ℤ), x 3 2 = ↑z + 1 / 2) ↔ x 0 0 = -1) 
→ y ∈ HW_group ∧ ((∃ (z : ℤ), y 3 2 = ↑z) ↔ y 0 0 = 1) 
∧ ((∃ (z : ℤ), y 3 2 = ↑z + 1 / 2) ↔ y 0 0 = -1) 
→ x * y ∈ HW_group ∧ ((∃ (z : ℤ), (x * y) 3 2 = ↑z) ↔ (x * y) 0 0 = 1) 
∧ ((∃ (z : ℤ), (x * y) 3 2 = ↑z + 1 / 2) ↔ (x * y) 0 0 = -1) :=
begin
  rintros ⟨hx, hx2, hx3⟩ ⟨hy, hy2, hy3⟩,
    use HW_group.mul_mem' hx hy,
    have hxy32 := HW_mul_32 hx hy,
    rw HW_group_22_eq_00_mul_11 hy at hxy32,
    have hxy00 := HW_mul_00 hx hy,
    simp only [one_div, matrix.general_linear_group.coe_mul, 
      matrix.general_linear_group.coe_fn_eq_coe] at *,
    simp only [hxy32, hxy00],
    clear hxy32 hxy00,
    have neg_one_mul_neg_one : (-1 : ℚ) * (-1 : ℚ) = (1 : ℚ) :=
    by simp only [mul_one, mul_neg, neg_neg],
    cases HW_group_00 hx with hx00 hx00;
    cases HW_group_11 hy with hy11 hy11;
    cases HW_group_00 hy with hy00 hy00;
    split;
    split;
    simp only [matrix.general_linear_group.coe_fn_eq_coe] at hx00 hy11 hy00;
    simp only [implies_true_iff, iff_true, forall_exists_index, eq_self_iff_true,
      hy00, hy11, hx00, mul_one, one_mul, eq_self_iff_true, forall_true_left,
      one_ne_neg_one, one_ne_neg_one.symm, forall_false_left, 
      mul_neg, neg_neg, imp_false, not_exists] at ⊢ hx2 hx3 hy2 hy3;    
    try {cases hx2 with zx2 hx2};
    try {cases hx3 with zx3 hx3};
    try {cases hy2 with zy2 hy2};
    try {cases hy3 with zy3 hy3};
    simp only [mul_neg_one, mul_one, hx2, hx3, hy2, hy3];
    simp only [push_neg.not_eq, add_comm (2⁻¹ : ℚ),
      ← int.cast_add, int.cast_inj, exists_eq', ← int.cast_neg, add_left_inj,
      int_ne_int_add_half, int_ne_int_add_half', not_false_iff, forall_const, neg_add, two_inv,
      ← add_assoc, add_right_comm _ (2⁻¹ : ℚ), sub_eq_add_neg, add_halfes,
      int_cast_one_rat, int_cast_neg_one_rat]
end

lemma HW_group_32 {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(((∃ z : ℤ, g 3 2 = ↑z) ↔ g 0 0 = 1) 
∧ ((∃ z : ℤ, g 3 2 = ↑z + 1 / 2) ↔ g 0 0 = -1)) :=
begin
  suffices : g ∈ HW_group 
  ∧ (((∃ z : ℤ, g 3 2 = ↑z) ↔ g 0 0 = 1) 
  ∧ ((∃ z : ℤ, g 3 2 = ↑z + 1 / 2) ↔ g 0 0 = -1)),
  {exact this.right},
  apply subgroup.closure_induction'' hg,
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      unfold HW_matrix.a,
      simp only with HW_matrix_simp,
      split,
      { simp only [eq_self_iff_true, iff_true],
        use 0,
        refl },
      { simp only [not_exists, one_ne_neg_one, iff_false, one_div],
        exact int_ne_int_add_half 0 }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      unfold HW_matrix.b,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_ne_neg_one.symm, not_exists, one_div, iff_false],
        exact half_ne_int },
      { simp only [eq_self_iff_true, iff_true, one_div],
        use 0,
        simp only [int.cast_zero, zero_add] }}},
  { intros x hx,
    cases hx with ha hb,
    { rw ha,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      rw GL_inv,
      unfold HW_matrix.a,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_div, eq_self_iff_true, iff_true],
        use 0,
        refl },
      { simp only [one_ne_neg_one, not_exists, one_div, iff_false],
        exact int_ne_int_add_half 0 }},
    { rw set.mem_singleton_iff at hb,
      rw hb,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      rw GL_inv,
      unfold HW_matrix.b,
      simp only with HW_matrix_simp,
      split,
      { simp only [one_ne_neg_one.symm, not_exists, one_div, iff_false, neg_one_div, two_inv,
          sub_eq_neg_add, int_cast_neg_one_rat'],
        exact half_ne_int },
      { simp only [eq_self_iff_true, iff_true, one_div],
        use 0,
        simp only [int.cast_zero, zero_add] }}},
  { intros,
    use HW_group.one_mem',
    rw HW_group.one_def,
    simp only with HW_matrix_simp,
    split,
    { simp only [eq_self_iff_true, iff_true],
      use 0,
      refl },
    { simp [one_ne_neg_one],
      exact int_ne_int_add_half 0 }},
  { intros x y,
    exact HW_group_32_help x y }
end

lemma HW_group_32' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(∃ z : ℤ, g 3 2 = ↑z) ↔ g 0 0 = 1 := and.elim_left (HW_group_32 hg)

lemma HW_group_32'' {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
(¬∃ z : ℤ, g 3 2 = ↑z) ↔ g 0 0 = -1 := 
begin
  rw and.elim_left (HW_group_32 hg),
  cases HW_group_00 hg;
  norm_num [h]
end

lemma HW_group_ext {g₁ g₂ : GL (fin 4) ℚ} (hg₁ : g₁ ∈ HW_group) (hg₂ : g₂ ∈ HW_group) :
g₁ = g₂ ↔ g₁ 3 0 = g₂ 3 0 ∧ g₁ 3 1 = g₂ 3 1 ∧ g₁ 3 2 = g₂ 3 2 :=
begin
  split,
  { intro h,
    simp[h] },
  { rintro ⟨h0, h1, h2⟩,
    apply formX_unique g₁ hg₁ g₂ hg₂,
    unfold formX HW_element,
    simp only [HW_group_00' hg₁, HW_group_00' hg₂, HW_group_11' hg₁, HW_group_11' hg₂,
      HW_group_22' hg₁, HW_group_22' hg₂, pm.pm_one_sign'_mul],
    --apply HW_matrix_ext,
    have h00 : g₁ 0 0 = g₂ 0 0,
    { 
      cases HW_group_00 hg₁,
      { have j := (HW_group_31 hg₁).elim_left,
        simp only [h, h1, eq_self_iff_true, iff_true] at j,
        cases j with z hz,
        rw h,
        symmetry,
        rw ← (HW_group_31 hg₂).elim_left,
        use z,
        exact hz },
      { have j := (HW_group_31 hg₁).elim_right,
        simp only [h, h1, eq_self_iff_true, iff_true] at j,
        cases j with z hz,
        rw h,
        symmetry,
        rw ← (HW_group_31 hg₂).elim_right,
        use z,
        exact hz}
    },
    have h11 : g₁ 1 1 = g₂ 1 1,
    { 
      cases HW_group_11 hg₁,
      { have j := (HW_group_30 hg₁).elim_left,
        simp only [h, h0, eq_self_iff_true, iff_true] at j,
        cases j with z hz,
        rw h,
        symmetry,
        rw ← (HW_group_30 hg₂).elim_left,
        use z,
        exact hz },
      { have j := (HW_group_30 hg₁).elim_right,
        simp only [h, h0, eq_self_iff_true, iff_true] at j,
        cases j with z hz,
        rw h,
        symmetry,
        rw ← (HW_group_30 hg₂).elim_right,
        use z,
        exact hz}
    },
    simp [h0, h1, h2, h00, h11]
  }
end

lemma HW_group_ext' {g₁ g₂ : HW_group} :
g₁ = g₂ ↔ g₁ 3 0 = g₂ 3 0 ∧ g₁ 3 1 = g₂ 3 1 ∧ g₁ 3 2 = g₂ 3 2 :=
begin
  split,
  { intro h,
    simp [h]},
  { intro h,
    ext1,
    simpa [HW_group_ext] using h }
end

lemma HW_group_neq {g₁ g₂ : HW_group} :
g₁ ≠ g₂ ↔ ¬(g₁ 3 0 = g₂ 3 0 ∧ g₁ 3 1 = g₂ 3 1 ∧ g₁ 3 2 = g₂ 3 2) :=
begin
  simp [HW_group_ext']
end

def sq_eq_one {g : GL (fin 4) ℚ} (hg : g ∈ HW_group) :
g^2 = 1 → g = 1 :=
begin
  rw [sq, ← HW_group_has_formX hg],
  unfold formX HW_element,
  rw [HW_group.one_def, GL_mul_apply, GL_ext_iff],
  dsimp only,
  cases HW_group_00 hg with h00 h00;
  cases HW_group_11 hg with h11 h11;
  simp [← HW_matrix_ext_iff, h00, h11],
  { intros h1 h2 h3,
    use [h1, h2, h3] },
  { simp [one_ne_neg_one.symm],
    intro h30,
    have h : ∃ (z : ℤ), g 3 0 = ↑z,
    { use 0,
      exact h30 },
    have := ((HW_group_30 hg).left).1,
    specialize this h,
    rw this at h11,
    exact one_ne_neg_one h11 },
  { simp [one_ne_neg_one.symm],
    intro h31,
    have h : ∃ (z : ℤ), g 3 1 = ↑z,
    { use 0,
      exact h31 },
    have := ((HW_group_31 hg).left).1,
    specialize this h,
    rw this at h00,
    exact one_ne_neg_one h00 },
  { simp [one_ne_neg_one.symm],
    intro h32,
    have h : ∃ (z : ℤ), g 3 2 = ↑z,
    { use 0,
      exact h32 },
    have := ((HW_group_32 hg).left).1,
    specialize this h,
    rw this at h00,
    exact one_ne_neg_one h00 }
end

@[class]
structure torsion_free_group (α : Type*) [group α] : Prop :=
(torsion_free : ∀ (g : α) (n : ℕ), n ≠ 0 → g^n = 1 → g = 1)

def torsion_element {α : Type*} [group α] (g : α) := ∃ n : ℕ, n ≠ 0 ∧ g^n = 1

lemma torsion_free_iff_no_torsion_element (α : Type*) [group α] : 
(∀ (g : α), g ≠ 1 → ¬torsion_element g) ↔ torsion_free_group α :=
begin
  unfold torsion_element,
  split,
  { intro h,
    refine {torsion_free := _},
    intros g n hn hg,
    by_cases hg2 : g = 1,
    { exact hg2 },
    { specialize h g hg2,
      contrapose h,
      push_neg,
      use [n, hn, hg] }},
  { intros t g hg h,
    cases h with n h,
    cases h with hn hg2,
    have tf := t.torsion_free,
    specialize tf g n hn hg2,
    contrapose hg,
    exact not_not.mpr tf }
end

lemma torsion_element_square {α : Type*} [group α] (g : α) :
torsion_element g ↔ ∃ n : ℕ, n ≠ 0 ∧ (g^2)^n = 1 :=
begin
  unfold torsion_element,
  split,
  { intro h,
    cases h with n h2,
    cases h2 with hn hg,
    use [n, hn],
    rw [pow_right_comm, hg, one_pow] },
  { intro h,
    cases h with n h2,
    cases h2 with hn hg,
    use [2 * n, mul_ne_zero two_ne_zero hn],
    rw pow_mul,
    exact hg }
end

instance : torsion_free_group HW_group := 
begin
  rw ← torsion_free_iff_no_torsion_element,
  intros g g1,
  rw torsion_element_square,
  push_neg,
  intros n hn,
  contrapose g1,
  simp only [not_not] at ⊢ g1,
  have g' := set_like.coe_mem g,
  have g'' := set_like.coe_mem (g^2),
  have g''' := HW_group.mul_mem' g' g',
  have g_sq_diag_one := square_diag_one g',
  simp only [← sq, subgroup.mem_carrier] at g''',
  have g_pow := diag_one_pow g''' n g_sq_diag_one,
  rw subtype.ext_iff at g1,
  simp only [matrix.general_linear_group.coe_fn_eq_coe, units.coe_pow] at g_pow,
  simp only [g_pow, subgroup.coe_pow, subgroup.coe_one] at g1,
  unfold HW_element at g1,
  rw [HW_group.one_def, GL_ext_iff] at g1,
  simp only [HW_group.one_def, GL_ext_iff, pm.pm_one_one] at g1,
  rw ← HW_matrix_ext_iff at g1,
  simp only [hn, true_and, false_or, eq_self_iff_true, nat.cast_eq_zero, mul_eq_zero] at g1,
  have : g^2 = 1,
  { have gX''' := HW_group_has_formX g''',
    have gX'' := HW_group_has_formX g'',
    ext1,
    rw ← gX'',
    obtain ⟨g_sq_00, g_sq_11, _⟩ := g_sq_diag_one,
    unfold formX HW_element,
    simp only [g_sq_00, g_sq_11, neg_one_mul, pm.pm_one_sign'_mul, subgroup.coe_pow,
      subgroup.coe_one, units.coe_pow],
    rw [HW_group.one_def, GL_ext_iff],
    apply HW_matrix_ext,
    simp only [g1, mul_one, eq_self_iff_true, pm.pm_one_one, and_self, pm.sign'_pos, zero_lt_one,
      matrix.general_linear_group.coe_fn_eq_coe, units.coe_pow],
  },
  rw subtype.ext_iff at ⊢ this,
  apply sq_eq_one g',
  simpa,
end

end torsion_free