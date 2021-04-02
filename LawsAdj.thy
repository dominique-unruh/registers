theory LawsAdj
imports AxiomsAdj Laws
begin

notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)
notation comp_update (infixl "*\<^sub>u" 55)

declare upd_adjoint_id[simp]
declare upd_adjoint_involution[simp]

lemma update_hom_sandwich[simp]: \<open>update_hom (sandwich a)\<close>
  unfolding sandwich_def 
  apply (rule update_comp_hom_is_hom)
  apply (rule hom_comp_update_is_hom)
  sorry

lemma sandwich_id[simp]: "sandwich id_update = id"
  unfolding sandwich_def by auto

lemma sandwich_lvalue[simp]:
  fixes a :: \<open>('a::domain, 'b::domain) update_nonsquare\<close>
  assumes \<open>unitary_update a\<close>
  shows \<open>lvalue (sandwich a)\<close>
proof -
  note assms update_hom_sandwich
  moreover have \<open>sandwich a id_update = id_update\<close>
    using assms by (auto simp: sandwich_def unitary_update_def)
  moreover have \<open>sandwich a (x *\<^sub>u y) = sandwich a x *\<^sub>u sandwich a y\<close> for x y
    using assms apply (auto simp: sandwich_def unitary_update_def)
    by (metis (no_types, lifting) comp_update_assoc id_update_left)
  moreover have \<open>sandwich a (upd_adjoint x) = upd_adjoint (sandwich a x)\<close> for x
    apply (auto simp: sandwich_def unitary_update_def upd_adjoint_comp)
    by (simp add: comp_update_assoc)
  ultimately show ?thesis
    apply (rule_tac lvalue_sandwhich_axiom)
    by assumption+
qed

end
