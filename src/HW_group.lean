import HW_matrix

@[derive group]
def HW_group : subgroup (GL (fin 4) ℚ) := subgroup.closure {HW_matrix.a, HW_matrix.b}

namespace HW_group

def a : HW_group := ⟨HW_matrix.a, subgroup.subset_closure (set.mem_insert _ _) ⟩

def b : HW_group := ⟨HW_matrix.b, 
subgroup.subset_closure (by simp only [set.mem_insert_iff, set.mem_singleton, or_true])⟩

def x : HW_group := a ^ 2

def y : HW_group := b ^ 2

def z : HW_group := (a * b) ^ 2

def lt : HW_group → HW_group → Prop :=
λ ⟨g₁, _⟩ ⟨g₂, _⟩, HW_matrix.lt g₁ g₂

instance : has_lt HW_group := ⟨lt⟩

instance : decidable_rel HW_group.has_lt.lt :=
begin
  intros g₁ g₂,
  cases g₁, cases g₂, dsimp at *,
  apply HW_matrix.lt.decidable_rel,
end

instance : is_irrefl HW_group lt :=
begin
  tidy,
end

lemma lt_def {g₁ g₂ : HW_group} : g₁ < g₂ ↔ 
  (g₁.val 3 0 < g₂.val 3 0) ∨ ((g₁.val 3 0 = g₂.val 3 0) ∧ (g₁.val 3 1 < g₂.val 3 1)) ∨ 
  ((g₁.val 3 0 = g₂.val 3 0) ∧ (g₁.val 3 1 = g₂.val 3 1) ∧ (g₁.val 3 2 < g₂.val 3 2)) :=
begin
  tidy,
end

lemma inv_apply {g : HW_group} {g_GL : GL (fin 4) ℚ} 
{hg : g_GL ∈ HW_group} {hg_inv : g_GL⁻¹ ∈ HW_group} 
{hg2 : g = ⟨g_GL, hg⟩} :
g⁻¹ = ⟨g_GL⁻¹, hg_inv⟩ :=
begin
  rw hg2,
  refl
end

lemma inv_apply' {g : HW_group} {g_GL : GL (fin 4) ℚ} 
{hg : g_GL ∈ HW_group} {hg_inv : g_GL⁻¹ ∈ HW_group} 
{hg2 : g = ⟨g_GL, hg⟩} :
(⟨g_GL, hg⟩ : HW_group) ⁻¹ = ⟨g_GL⁻¹, hg_inv⟩ :=
begin
  refl
end

lemma mul_apply {g h : HW_group} {g_GL h_GL : GL (fin 4) ℚ} 
{hg : g_GL ∈ HW_group} {hh : h_GL ∈ HW_group} 
{hg2 : g = ⟨g_GL, hg⟩} {hh2 : h = ⟨h_GL, hh⟩} :
g * h = ⟨g_GL * h_GL, subgroup.mul_mem' _ hg hh⟩ :=
begin
  rw [hg2, hh2],
  refl
end

lemma HW_apply {g : GL (fin 4) ℚ} {i j : fin 4} (h : g ∈ HW_group) : 
(⟨g, h⟩ : HW_group) i j =  g.val i j := rfl

lemma one_def : (1 : (GL (fin 4) ℚ)) = 
  { val := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0, 0, 1]],
  inv := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, 1, 0], 
  ![0, 0, 0, 1]],
  val_inv := by simp[HW_matrix.one_def],
  inv_val := by simp[HW_matrix.one_def] } :=
begin
  ext1,
  simp [HW_matrix.one_def],
end

lemma HW_one_def : (1 : HW_group) = 
  { val := 1,
    property := HW_group.one_mem' }:=
begin
  ext1,
  simp [HW_matrix.one_def],
end

lemma ab_neq_one : a * b ≠ 1 :=
begin
  unfold a b,
  unfold HW_matrix.a HW_matrix.b,
  simp only [ne.def, subtype.ext_iff, subgroup.coe_pow, subgroup.coe_inv, subgroup.coe_mul, 
    subgroup.coe_one, subtype.coe_mk, units.ext_iff, sq, matrix_mul_apply, matrix.mul_eq_mul,
    matrix.general_linear_group.coe_mul, units.coe_mk,units.inv_mk, units.inv_eq_coe_inv,
    mul_inv_rev, ← HW_matrix_ext_iff, HW_group.one_def,
    neg_one_ne_one, one_ne_neg_one, one_ne_zero, mul_neg, mul_one, neg_neg, neg_add_rev, 
    neg_zero, neg_eq_zero, false_and, and_false, not_false_iff, zero_add, zero_mul, add_zero, 
    one_div, add_right_neg, add_left_neg, inv_eq_zero, bit0_eq_zero, or_self, div_eq_zero_iff, 
    half_add_half, add_halves', add_left_eq_self, add_self_eq_zero],
end

lemma a_def : (a : (GL (fin 4) ℚ)) = 
{ val := ![![1, 0, 0, 0],
  ![0, -1, 0, 0], 
  ![0, 0, -1, 0], 
  ![1/2, 0, 0, 1]],
  inv := ![![1, 0, 0, 0], 
  ![0, -1, 0, 0],
  ![0, 0, -1, 0], 
  ![-1/2, 0, 0, 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def]} := rfl

lemma b_def : (b : (GL (fin 4) ℚ)) = 
{ val := ![![-1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, -1, 0], 
  ![0, 1/2, 1/2, 1]],
  inv := ![![-1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, -1, 0], 
  ![0, -1/2, 1/2, 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] } := rfl

lemma a_inv_def_help : 
({inv := ![![1, 0, 0, 0],
  ![0, -1, 0, 0], 
  ![0, 0, -1, 0], 
  ![1/2, 0, 0, 1]],
  val := ![![1, 0, 0, 0], 
  ![0, -1, 0, 0],
  ![0, 0, -1, 0], 
  ![-1/2, 0, 0, 1]],
 val_inv := by simp [HW_matrix.one_def],
 inv_val := by simp [HW_matrix.one_def]} : GL (fin 4) ℚ)
∈ HW_group :=
begin
  have h := set_like.coe_mem HW_group.a⁻¹,
  unfold HW_group.a HW_matrix.a at h,
  simpa using h
end

lemma a_inv_def : HW_group.a⁻¹ =
⟨{ inv := ![![1, 0, 0, 0],
  ![0, -1, 0, 0], 
  ![0, 0, -1, 0], 
  ![1/2, 0, 0, 1]],
  val := ![![1, 0, 0, 0], 
  ![0, -1, 0, 0],
  ![0, 0, -1, 0], 
  ![-1/2, 0, 0, 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def]}, 
  a_inv_def_help ⟩ :=
begin
  unfold a HW_matrix.a,
  refl
end

lemma b_inv_def_help : 
({val := ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, (-1) / 2, 1 / 2, 1]],
 inv := ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 1 / 2, 1 / 2, 1]],
 val_inv := by simp [HW_matrix.one_def],
 inv_val := by simp [HW_matrix.one_def]} : GL (fin 4) ℚ)
∈ HW_group :=
begin
  have h := set_like.coe_mem HW_group.b⁻¹,
  unfold HW_group.b HW_matrix.b at h,
  simp only [one_div, subgroup.coe_inv, subgroup.coe_mk, units.inv_mk] at h,
  simp [h]
end

lemma b_inv_def : HW_group.b⁻¹ =
⟨{ inv := ![![-1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, -1, 0], 
  ![0, 1/2, 1/2, 1]],
  val := ![![-1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, -1, 0], 
  ![0, -1/2, 1/2, 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] }, 
  b_inv_def_help ⟩ :=
begin
  unfold b HW_matrix.b,
  refl
end

lemma x_def : (x : (GL (fin 4) ℚ)) = 
{ val := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![1, 0, 0, 1]],
  inv := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, 1, 0], 
  ![-1, 0, 0, 1]],
  val_inv := by simp[HW_matrix.one_def],
  inv_val := by simp[HW_matrix.one_def] } :=
begin
  unfold x,
  ext1,
  field_simp [sq, HW_matrix.one_def, a_def]
end

lemma y_def : (y : (GL (fin 4) ℚ)) = 
{ val := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 1, 0, 1]],
  inv := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, 1, 0], 
  ![0, -1, 0, 1]],
  val_inv := by simp[HW_matrix.one_def],
  inv_val := by simp[HW_matrix.one_def] } :=
begin
  unfold y,
  ext1,
  field_simp [sq, HW_matrix.one_def, b_def]
end

lemma z_def : (z : (GL (fin 4) ℚ)) = 
{ val := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0, 1, 1]],
  inv := ![![1, 0, 0, 0], 
  ![0, 1, 0, 0],
  ![0, 0, 1, 0], 
  ![0, 0, -1, 1]],
  val_inv := by simp [HW_matrix.one_def],
  inv_val := by simp [HW_matrix.one_def] } :=
begin
  unfold z,
  ext1,
  field_simp [sq, HW_matrix.one_def, b_def, a_def]
end

lemma x_pow (n : ℤ) : (x : (GL (fin 4) ℚ)) ^ n = 
{ val := ![![1, 0, 0, 0],
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

lemma y_pow (n : ℤ) : (y : (GL (fin 4) ℚ)) ^ n 
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

lemma z_pow (n : ℤ) : (z : (GL (fin 4) ℚ)) ^ n =
{ val :=![![1, 0, 0, 0],
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

lemma rel_1 : a⁻¹ * b ^ 2 * a * b ^ 2 = 1 :=
begin
  ext1,
  exact HW_matrix.rel_1,
end

lemma rel_2 : b⁻¹ * a ^ 2 * b * a ^ 2 = 1 :=
begin
  ext1,
  exact HW_matrix.rel_2,
end

def f_gen : generator → HW_group
| generator.a := a
| generator.b := b

def lift_f_gen : free_group generator →* ↥HW_group := free_group.lift f_gen

@[simp]lemma lift_f_gen_a : lift_f_gen gen.a = a := free_group.lift.of

@[simp]lemma lift_f_gen_b : lift_f_gen gen.b = b := free_group.lift.of

lemma h_f_gen : ∀ (r : free_group generator), r ∈ gen.rels → lift_f_gen r = 1 :=
begin
  rintros r (rfl|(rfl:r=_));
  simp only [map_mul, map_pow, lift_f_gen_a, lift_f_gen_b, map_inv, rel_1, rel_2],
end

def f : HW →* HW_group := presented_group.to_group h_f_gen

lemma f_a : f HW.a = a := 
begin
  unfold f HW.a HW.to_HW,
  simp only [presented_group.to_group.of],
  refl
end

lemma f_b : f HW.b = b := 
begin
  unfold f HW.b HW.to_HW,
  simp only [presented_group.to_group.of],
  refl
end

lemma a_neq_b: a ≠ b := 
begin
  unfold a b,
  simp only [subtype.mk_eq_mk, ne.def],
  unfold HW_matrix.a HW_matrix.b,
  rw GL_ext_iff,
  simp only [one_div],
  by_contra,
  rw ← HW_matrix_ext_iff at h,
  simpa using h
end

lemma HW.a_neq_b: HW.a ≠ HW.b := 
begin
  by_contra,
  have h2 : a = b,
  { rw ← f_a,
    rw ← f_b,
    rw h },
  apply a_neq_b,
  exact h2
end

/- lemma lift_f_gen_range : set.range lift_f_gen = ↑(subgroup.closure (set.range f_gen)) := free_group.lift.range_eq_closure

lemma f_gen_range' : set.range f_gen = {a, b} :=
begin
  ext,
  simp,
  split,
    {intro h,
    cases h with h1 h2,
    cases h1 with c d,
    rw ← h2,
    left,
    refl,
    rw ← h2,
    right,
    refl
    },
    {intro h,
    cases h,
    rw h,
    use generator.a,
    refl,
    rw h,
    use generator.b,
    refl}
end

lemma lift_f_gen_range' : set.range lift_f_gen = ↑(subgroup.closure ({a, b} : set HW_group)) := 
begin
  rw ← f_gen_range',
  exact free_group.lift.range_eq_closure
end -/

lemma HW_group_word_exist {g : (GL (fin 4) ℚ)} (hg : g ∈ HW_group) :
∃l : list (generator × bool), HW_matrix.from_word l = g :=
begin
  suffices : (g ∈ HW_group) ∧ (∃ (l : list (generator × bool)), HW_matrix.from_word l = g),
  {exact this.right},
  apply subgroup.closure_induction hg,
  {
    intros x hx,
    cases hx,
    { rw hx,
      split,
      { apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      use ([(generator.a, tt)]),
      simp only [HW_matrix.from_word_nil, HW_matrix.from_word_cons, 
        mul_one, HW_matrix.pre_from_word_a_tt] },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      split,
      { apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      use ([(generator.b, tt)]),
      simp }},
  { use HW_group.one_mem',
    use @list.nil (generator × bool),
    refl },
  { rintros x y ⟨hx1, lx, hx2⟩ ⟨hy1, ly, hy2⟩,
    use HW_group.mul_mem' hx1 hy1,
    use lx ++ ly,
    simp [hx2, hy2] },
  { rintros x ⟨hx1, l, hx2⟩,
    use [HW_group.inv_mem' hx1, (list.reverse (HW_matrix.from_word_reverse_bool l))],
    simp [hx2] }
end

lemma from_word_mem_HW_group (l: list (generator × bool)) :
HW_matrix.from_word l ∈ HW_group :=
begin
  induction l,
  { simp only [HW_matrix.from_word_nil],
    exact HW_group.one_mem' },
  { cases l_hd with gen b,
    cases gen with a b;
    cases b with ff tt,
    { simp only [HW_matrix.from_word_cons, HW_matrix.pre_from_word_a_ff],
      apply HW_group.mul_mem' _ l_ih,
      apply HW_group.inv_mem,
      apply subgroup.subset_closure,
      exact set.mem_insert HW_matrix.a {HW_matrix.b} },
    { simp only [HW_matrix.from_word_cons, HW_matrix.pre_from_word_a_tt],
      apply HW_group.mul_mem' _ l_ih,
      apply subgroup.subset_closure,
      exact set.mem_insert HW_matrix.a {HW_matrix.b} },
    { simp only [HW_matrix.from_word_cons, HW_matrix.pre_from_word_b_ff],
      apply HW_group.mul_mem' _ l_ih,
      apply HW_group.inv_mem,
      apply subgroup.subset_closure,
      simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
    { simp only [HW_matrix.from_word_cons, HW_matrix.pre_from_word_b_tt],
      apply HW_group.mul_mem' _ l_ih,
      apply subgroup.subset_closure,
      simp only [set.mem_insert_iff, set.mem_singleton, or_true] }}
end

theorem HW_group_induction 
{p :(GL (fin 4) ℚ) → Prop} {g : (GL (fin 4) ℚ)}
(hg : g ∈ HW_group)
(h1 : p 1)
(ha : ∀ (x : (GL (fin 4) ℚ)), x ∈ HW_group → p x → p (HW_matrix.a * x))
(hb : ∀ (x : (GL (fin 4) ℚ)), x ∈ HW_group → p x → p (HW_matrix.b * x))
(ha_inv : ∀ (x : (GL (fin 4) ℚ)), x ∈ HW_group → p x → p (HW_matrix.a⁻¹ * x))
(hb_inv : ∀ (x : (GL (fin 4) ℚ)), x ∈ HW_group → p x → p (HW_matrix.b⁻¹ * x)) :
p g :=
begin
  suffices : (g ∈ HW_group) ∧ p g,
  { exact this.right },
  apply subgroup.closure_induction'' hg,
  { intros x hx,
    cases hx,
    { rw hx,
      split,
      { apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      specialize ha 1 HW_group.one_mem' h1,
      rw mul_one at ha,
      exact ha },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      split,
      { apply subgroup.subset_closure,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
      specialize hb 1 HW_group.one_mem' h1,
      rw mul_one at hb,
      exact hb }},
  { rintros x hx,
    cases hx,
    { rw hx,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        exact set.mem_insert HW_matrix.a {HW_matrix.b} },
      specialize ha_inv 1 HW_group.one_mem' h1,
      rw mul_one at ha_inv,
      exact ha_inv },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      split,
      { apply HW_group.inv_mem',
        apply subgroup.subset_closure,
        simp[set.mem_insert_iff, set.mem_singleton, or_true] },
      specialize hb_inv 1 HW_group.one_mem' h1,
      rw mul_one at hb_inv,
      exact hb_inv }},
  { use HW_group.one_mem',
    exact h1 },
  { rintros x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩,
    use HW_group.mul_mem' hx1 hy1,
    have x_word := HW_group_word_exist hx1,
    have y_word := HW_group_word_exist hy1,
    cases x_word with xl hxl,
    cases y_word with yl hyl,
    rw ← hxl,
    clear hxl,
    induction xl,
    { simp,
      exact hy2 },
    { cases xl_hd with xl_hd_gen xl_hd_b,
      cases xl_hd_gen; cases xl_hd_b; simp,
      { rw mul_assoc,
        apply ha_inv (HW_matrix.from_word xl_tl * y) (HW_group.mul_mem' _ hy1),
        apply xl_ih,
        apply from_word_mem_HW_group },
      { rw mul_assoc,
        apply ha (HW_matrix.from_word xl_tl * y) (HW_group.mul_mem' _ hy1),
        apply xl_ih,
        apply from_word_mem_HW_group },
      { rw mul_assoc,
        apply hb_inv (HW_matrix.from_word xl_tl * y) (HW_group.mul_mem' _ hy1),
        apply xl_ih,
        apply from_word_mem_HW_group },
      { rw mul_assoc,
        apply hb (HW_matrix.from_word xl_tl * y) (HW_group.mul_mem' _ hy1),
        apply xl_ih,
        apply from_word_mem_HW_group }}}
end
  
end HW_group