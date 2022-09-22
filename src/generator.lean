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
import data.nat.parity
import data.zmod.basic
import algebra.group.defs

@[derive decidable_eq]
inductive generator : Type
| a : generator
| b : generator

namespace gen

def a : free_group generator := free_group.of generator.a

def b : free_group generator := free_group.of generator.b

def rels : set (free_group generator) :=
{b⁻¹ * a^2 * b * a^2,
a⁻¹ * b^2 * a * b^2}

def to_word : free_group generator → list (generator × bool) := free_group.to_word

end gen