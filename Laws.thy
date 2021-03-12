theory Laws
  imports Axioms
    "HOL-Library.Rewrite"
begin

unbundle lvalue_notation

definition "tensor_maps_hom F G = tensor_lift (\<lambda>a b. F a \<otimes> G b)"

lemma maps_2hom_F_tensor_G[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>maps_2hom (\<lambda>a b. F a \<otimes> G b)\<close>
proof -
  have \<open>maps_hom (\<lambda>b. F a \<otimes> G b)\<close> for a
    using \<open>maps_hom G\<close> apply (rule comp_maps_hom[of G \<open>\<lambda>b. F a \<otimes> b\<close>, unfolded comp_def])
    using maps_2hom_def tensor_2hom by auto
  moreover have \<open>maps_hom (\<lambda>a. F a \<otimes> G b)\<close> for b
    using \<open>maps_hom F\<close> apply (rule comp_maps_hom[of F \<open>\<lambda>a. a \<otimes> G b\<close>, unfolded comp_def])
    using maps_2hom_def tensor_2hom by auto
  ultimately show ?thesis
    unfolding maps_2hom_def by auto
qed

lemma tensor_maps_hom_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (tensor_maps_hom F G)"
  unfolding tensor_maps_hom_def apply (rule tensor_lift_hom) by simp

lemma tensor_maps_hom_apply[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows "tensor_maps_hom F G (a \<otimes> b) = F a \<otimes> G b"
  unfolding tensor_maps_hom_def 
  using tensor_existence maps_2hom_F_tensor_G assms
  by metis

bundle lvalue_notation begin
unbundle lvalue_notation
notation tensor_maps_hom (infixr "\<otimes>\<^sub>h" 70)
end

bundle no_lvalue_notation begin
unbundle lvalue_notation
no_notation tensor_maps_hom (infixr "\<otimes>\<^sub>h" 70)
end
