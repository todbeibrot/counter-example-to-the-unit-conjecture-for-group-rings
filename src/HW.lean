import generator

@[derive group]
def HW := presented_group gen.rels

namespace HW    --Hantzsche-Wendt groups

def to_HW (x : generator) : HW := presented_group.of x

def mk' : free_group generator →* HW := quotient_group.mk' _

def a := to_HW generator.a

def b := to_HW generator.b

def x := a^2

def y := b^2

def z := (a * b)^2

@[simp]lemma mk'_a : mk' gen.a = a := by refl

@[simp]lemma mk'_b : mk' gen.b = b := by refl

lemma mk'_eq_one_iff {x : free_group generator} : 
mk' x = 1 ↔ x ∈ subgroup.normal_closure gen.rels := 
by exact quotient_group.eq_one_iff x

lemma rel_1: a⁻¹ * b^2 * a * b^2 = 1 := 
begin
  have h : a⁻¹ * b ^ 2 * a * b ^ 2 =
    mk' ((free_group.of generator.a)⁻¹ * (free_group.of generator.b)^2 
    * (free_group.of generator.a) * (free_group.of generator.b)^2) 
    := rfl,
  rw [h, mk'_eq_one_iff],
  apply subgroup.closure_le_normal_closure,
  apply subgroup.subset_closure,
  unfold gen.rels,
  simp only [set.mem_insert_iff, set.mem_singleton_iff],
  right,
  unfold gen.a gen.b
end

lemma rel_2: b⁻¹ * a^2 * b * a^2 = 1 := 
begin
  have h: b⁻¹ * a ^ 2 * b * a ^ 2 = 
    mk' ((free_group.of generator.b)⁻¹ * (free_group.of generator.a)^2 
    * (free_group.of generator.b) * (free_group.of generator.a)^2) 
    := rfl,
  rw [h, mk'_eq_one_iff],
  apply subgroup.closure_le_normal_closure,
  apply subgroup.subset_closure,
  unfold gen.rels,
  simp only [set.mem_insert_iff, set.mem_singleton_iff],
  left,
  unfold gen.a gen.b
end

--lemma a_neq_b: a ≠ b 
--moved to HW_group

end HW