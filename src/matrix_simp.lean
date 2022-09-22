import group_theory.presented_group
import tactic
import group_theory.quotient_group
import data.matrix.basic
import data.matrix.notation
import linear_algebra.general_linear_group
import group_theory.subgroup.basic
import linear_algebra.matrix.determinant
import data.matrix.notation
import linear_algebra.matrix.determinant
import group_theory.perm.fin
import tactic.norm_swap
import linear_algebra.determinant
import linear_algebra.matrix.block
import data.real.sign

mk_simp_attribute HW_matrix_simp "reduces a acces to an element of a matrix to the element"

attribute [HW_matrix_simp] units.coe_mk matrix.general_linear_group.coe_fn_eq_coe

@[HW_matrix_simp]
lemma GL_simp (g : GL (fin 4) ℚ) (i j : ℕ) :
g i j = g.val i j := rfl

@[HW_matrix_simp]
lemma HW_simp00 {g00 g11 g22 g30 g31 g32 g33 : ℚ} :
((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, g33]]) : matrix (fin 4) (fin 4) ℚ) 0 0 = g00 := rfl

@[HW_matrix_simp]
lemma HW_simp11 {g00 g11 g22 g30 g31 g32 g33 : ℚ} :
((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, g33]]) : matrix (fin 4) (fin 4) ℚ) 1 1 = g11 := rfl

@[HW_matrix_simp]
lemma HW_simp22 {g00 g11 g22 g30 g31 g32 g33 : ℚ} :
((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, g33]]) : matrix (fin 4) (fin 4) ℚ) 2 2 = g22 := rfl

@[HW_matrix_simp]
lemma HW_simp30 {g00 g11 g22 g30 g31 g32 g33 : ℚ} :
((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, g33]]) : matrix (fin 4) (fin 4) ℚ) 3 0 = g30 := rfl

@[HW_matrix_simp]
lemma HW_simp31 {g00 g11 g22 g30 g31 g32 g33 : ℚ} :
((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, g33]]) : matrix (fin 4) (fin 4) ℚ) 3 1 = g31 := rfl

@[HW_matrix_simp]
lemma HW_simp32 {g00 g11 g22 g30 g31 g32 g33 : ℚ} :
((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, g33]]) : matrix (fin 4) (fin 4) ℚ) 3 2 = g32 := rfl

lemma GL_mul_apply {g h : GL (fin 4) ℚ} : g * h = 
{ val := g.val * h.val,
inv := h.inv * g.inv,
.. g*h } := rfl

lemma GL_mul_apply' {g h g_inv h_inv : matrix (fin 4) (fin 4) ℚ} 
(g_val_inv : g * g_inv = 1) (g_inv_val : g_inv * g = 1)
(h_val_inv : h * h_inv = 1) (h_inv_val : h_inv * h = 1) : 
({ val := g,
inv := g_inv,
val_inv := g_val_inv,
inv_val := g_inv_val } : GL (fin 4) ℚ)
*
({ val := h,
inv := h_inv,
val_inv := h_val_inv,
inv_val := h_inv_val } : GL (fin 4) ℚ)
= 
({ val := g * h,
inv := h_inv * g_inv,
val_inv := by rw [mul_assoc, ← mul_assoc h, h_val_inv, one_mul, g_val_inv],
inv_val := by rw [mul_assoc, ← mul_assoc g_inv, g_inv_val, one_mul, h_inv_val] } : GL (fin 4) ℚ)
:= rfl

lemma GL_inv (g : GL (fin 4) ℚ) :
g⁻¹ = { val := g.inv, inv := g.val, val_inv := g.inv_val, inv_val := g.val_inv }
:= by refl

lemma GL_ext_iff (g h : GL (fin 4) ℚ) : g = h ↔ g.val = h.val :=
begin
  split,
  { intro j,
    rw j },
  { intro j,
    have hg : g = {val:= g.val, inv := g.inv, val_inv := g.val_inv, inv_val := g.inv_val}, 
    { simp only [units.val_eq_coe, units.mk_coe] },    
    have hh : h = {val:= h.val, inv := h.inv, val_inv := h.val_inv, inv_val := h.inv_val},
    { simp only [units.val_eq_coe, units.mk_coe] },
    rw [hg, hh],
    simp only [units.val_eq_coe, units.mk_coe, j] }
end

lemma GL_ext (g h : GL (fin 4) ℚ) : g.val = h.val → g = h := (GL_ext_iff g h).mpr

@[HW_matrix_simp]
lemma matrix_mul_apply {g00 g11 g22 g30 g31 g32 : ℚ} {h00 h11 h22 h30 h31 h32 : ℚ} :
matrix.mul ((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, 1]]) : matrix (fin 4) (fin 4) ℚ)
 ((![![h00, 0, 0, 0], 
![0, h11, 0, 0], 
![0, 0, h22, 0],
![h30, h31, h32, 1]]) : matrix (fin 4) (fin 4) ℚ)
= ((![![g00 * h00, 0, 0, 0], 
![0, g11 * h11, 0, 0], 
![0, 0, g22 * h22, 0],
![g30 * h00 + h30, g31 * h11 + h31, g32 * h22 + h32, 1]]) : matrix (fin 4) (fin 4) ℚ) :=
begin
  ext1 i,
  ext1 j,
  fin_cases i; fin_cases j; simp,
end

@[HW_matrix_simp]
lemma HW_matrix_ext {g00 g11 g22 g30 g31 g32: ℚ} {h00 h11 h22 h30 h31 h32 : ℚ} :
g00 = h00 ∧ g11 = h11 ∧ g22 = h22 ∧ g30 = h30 ∧ g31 = h31 ∧ g32 = h32
→ ((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, 1]]) : matrix (fin 4) (fin 4) ℚ)
= ((![![h00, 0, 0, 0], 
![0, h11, 0, 0], 
![0, 0, h22, 0],
![h30, h31, h32, 1]]) : matrix (fin 4) (fin 4) ℚ) :=
begin
  intro j,
  simp[j],
end

lemma HW_matrix_ext_iff {g00 g11 g22 g30 g31 g32: ℚ} {h00 h11 h22 h30 h31 h32 : ℚ} :
g00 = h00 ∧ g11 = h11 ∧ g22 = h22 ∧ g30 = h30 ∧ g31 = h31 ∧ g32 = h32
↔ ((![![g00, 0, 0, 0], 
![0, g11, 0, 0], 
![0, 0, g22, 0],
![g30, g31, g32, 1]]) : matrix (fin 4) (fin 4) ℚ)
= ((![![h00, 0, 0, 0], 
![0, h11, 0, 0], 
![0, 0, h22, 0],
![h30, h31, h32, 1]]) : matrix (fin 4) (fin 4) ℚ) :=
begin
  split,
  { intro k,
    simp[k] },
  { intro k,
    rw ← matrix.ext_iff at k,
    use [k 0 0, k 1 1, k 2 2, k 3 0, k 3 1, k 3 2] }
end

@[HW_matrix_simp]
lemma HW_GL_ext {g00 g11 g22 g30 g31 g32: ℚ} {h00 h11 h22 h30 h31 h32 : ℚ} 
{g_inv g_val_inv g_inv_val} {h_inv h_val_inv h_inv_val}:
g00 = h00 ∧ g11 = h11 ∧ g22 = h22 ∧ g30 = h30 ∧ g31 = h31 ∧ g32 = h32
→ (({ val := ((![![g00, 0, 0, 0], 
  ![0, g11, 0, 0], 
  ![0, 0, g22, 0],
  ![g30, g31, g32, 1]]) : matrix (fin 4) (fin 4) ℚ),
  inv := g_inv,
  val_inv := g_val_inv,
  inv_val := g_inv_val }) :  GL (fin 4) ℚ)
= { val := ((![![h00, 0, 0, 0], 
  ![0, h11, 0, 0], 
  ![0, 0, h22, 0],
  ![h30, h31, h32, 1]]) : matrix (fin 4) (fin 4) ℚ),
  inv := h_inv,
  val_inv := h_val_inv,
  inv_val := h_inv_val }
 :=
begin
  intro j,
  apply GL_ext,
  exact HW_matrix_ext j
end

