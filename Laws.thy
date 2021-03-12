theory Laws
  imports Axioms
    "HOL-Library.Rewrite"
begin

unbundle lvalue_notation

subsection \<open>Elementary facts\<close>

declare tensor_2hom[simp]

lemma maps_hom_2hom_comp: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. G (F2 a b))\<close>
  unfolding maps_2hom_def 
  using comp_maps_hom[of \<open>\<lambda>a. F2 a _\<close> G]
  using comp_maps_hom[of \<open>\<lambda>b. F2 _ b\<close> G]
  unfolding o_def by auto

subsection \<open>Tensor product of homs\<close>

definition "tensor_maps_hom F G = tensor_lift (\<lambda>a b. F a \<otimes> G b)"

lemma maps_2hom_F_tensor_G[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>maps_2hom (\<lambda>a b. F a \<otimes> G b)\<close>
proof -
  have \<open>maps_hom (\<lambda>b. F a \<otimes> G b)\<close> for a
    using \<open>maps_hom G\<close> apply (rule comp_maps_hom[of G \<open>\<lambda>b. F a \<otimes> b\<close>, unfolded comp_def])
    using maps_2hom_def by (auto intro!: tensor_2hom)
  moreover have \<open>maps_hom (\<lambda>a. F a \<otimes> G b)\<close> for b
    using \<open>maps_hom F\<close> apply (rule comp_maps_hom[of F \<open>\<lambda>a. a \<otimes> G b\<close>, unfolded comp_def])
    using maps_2hom_def by (auto intro!: tensor_2hom)
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

lemma maps_2hom_F_tensor[simp]: \<open>maps_hom F \<Longrightarrow> maps_2hom (\<lambda>a b. F (a \<otimes> b))\<close>
  using tensor_2hom by (rule maps_hom_2hom_comp)

lemma tensor_extensionality:
  fixes F G :: \<open>('a::domain\<times>'b::domain, 'c::domain) maps_hom\<close>
  assumes [simp]: "maps_hom F" "maps_hom G"
  assumes "(\<And>a b. F (a \<otimes> b) = G (a \<otimes> b))"
  shows "F = G"
proof -
  have \<open>F = tensor_lift (\<lambda>a b. F (a \<otimes> b))\<close>
    by (rule tensor_uniqueness, auto)
  moreover have \<open>G = tensor_lift (\<lambda>a b. G (a \<otimes> b))\<close>
    by (rule tensor_uniqueness, auto)
  moreover note assms(3)
  ultimately show "F = G"
    by simp
qed

lemma left_tensor_hom[simp]: "maps_hom ((\<otimes>) a)"
  using maps_2hom_def tensor_2hom by blast

lemma right_tensor_hom[simp]: "maps_hom (\<lambda>a. (\<otimes>) a b)"
  using maps_2hom_def tensor_2hom by blast

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain, 'd::domain) maps_hom\<close>
  assumes [simp]: \<open>maps_hom F\<close> \<open>maps_hom G\<close>
  assumes "\<And>f g h. F (f \<otimes> g \<otimes> h) = G (f \<otimes> g \<otimes> h)"
  shows "F = G"
proof -
  from assms
  have "(F \<circ> (\<otimes>) a) (b \<otimes> c) = (G \<circ> (\<otimes>) a) (b \<otimes> c)" for a b c
    by auto
  then have "F \<circ> (\<otimes>) a = G \<circ> (\<otimes>) a" for a
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_maps_hom; simp)+
  then have "F (a \<otimes> bc) = G (a \<otimes> bc)" for a bc
    using comp_eq_elim by blast
  then show ?thesis
    by (rule tensor_extensionality[rotated -1]; simp)
qed


subsection \<open>Swap and assoc\<close>

definition \<open>swap = tensor_lift (\<lambda>a b. b \<otimes> a)\<close>

lemma swap_hom[simp]: "maps_hom swap"
  unfolding swap_def apply (rule tensor_lift_hom) 
  using tensor_2hom unfolding maps_2hom_def by auto

lemma swap_apply[simp]: "swap (a \<otimes> b) = (b \<otimes> a)"
  unfolding swap_def 
  apply (rule tensor_existence[THEN fun_cong, THEN fun_cong])
  using tensor_2hom unfolding maps_2hom_def by auto

subsection \<open>Pairs and compatibility\<close>

definition compatible :: \<open>('a::domain,'c::domain) maps_hom \<Rightarrow> ('b::domain,'c) maps_hom \<Rightarrow> bool\<close> where
  \<open>compatible F G \<longleftrightarrow> lvalue F \<and> lvalue G \<and> (\<forall>a b. F a \<circ>\<^sub>d G b = G b \<circ>\<^sub>d F a)\<close>

lemma compatibleI:
  assumes "lvalue F" and "lvalue G"
  assumes \<open>\<And>a b. (F a) \<circ>\<^sub>d (G b) = (G b) \<circ>\<^sub>d (F a)\<close>
  shows "compatible F G"
  using assms unfolding compatible_def by simp

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

definition pair :: \<open>('a::domain,'c::domain) maps_hom \<Rightarrow> ('b::domain,'c) maps_hom \<Rightarrow> ('a\<times>'b, 'c) maps_hom\<close> where
  \<open>pair F G = tensor_lift (\<lambda>a b. F a \<circ>\<^sub>d G b)\<close>

lemma maps_hom_F_comp_G1:
  assumes \<open>maps_hom G\<close>
  shows \<open>maps_hom (\<lambda>b. F a \<circ>\<^sub>d G b)\<close>
  using assms apply (rule comp_maps_hom[of G \<open>\<lambda>b. F a \<circ>\<^sub>d b\<close>, unfolded comp_def])
  using maps_2hom_def comp_2hom by auto

lemma maps_hom_F_comp_G2:
  assumes \<open>maps_hom F\<close>
  shows \<open>maps_hom (\<lambda>a. F a \<circ>\<^sub>d G b)\<close> 
    using assms apply (rule comp_maps_hom[of F \<open>\<lambda>a. a \<circ>\<^sub>d G b\<close>, unfolded comp_def])
    using maps_2hom_def comp_2hom by auto

lemma maps_2hom_F_comp_G[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>maps_2hom (\<lambda>a b. F a \<circ>\<^sub>d G b)\<close>
  unfolding maps_2hom_def
  using assms
  by (auto intro!: maps_hom_F_comp_G1 maps_hom_F_comp_G2)

lemma pair_hom[simp]:
  assumes "maps_hom F" and "maps_hom G"
  shows "maps_hom (pair F G)"
  unfolding pair_def apply (rule tensor_lift_hom) using assms by simp

lemma pair_apply[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>(pair F G) (a \<otimes> b) = (F a) \<circ>\<^sub>d (G b)\<close>
  unfolding pair_def 
  using tensor_existence maps_2hom_F_comp_G assms
  by metis

lemma pair_lvalue[simp]:
  assumes "compatible F G"
  shows "lvalue (pair F G)"
  apply (rule pair_lvalue_axiom[where F=F and G=G and p=\<open>pair F G\<close>])
  using assms by (auto simp: compatible_def lvalue_hom)
  
lemma compatible3:
  assumes [simp]: "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible (pair x y) z"
proof (rule compatibleI)
  have [simp]: \<open>lvalue x\<close> \<open>lvalue y\<close> \<open>lvalue z\<close>
    using assms compatible_def by auto
  then have [simp]: \<open>maps_hom x\<close> \<open>maps_hom y\<close> \<open>maps_hom z\<close>
    using lvalue_hom by blast+
  have "(pair (pair x y) z) ((f \<otimes> g) \<otimes> h) = (pair z (pair x y)) (h \<otimes> (f \<otimes> g))" for f g h
    apply auto using assms unfolding compatible_def
    by (metis comp_domain_assoc)
  then have "(pair (pair x y) z \<circ> swap \<circ> (\<otimes>) h) (f \<otimes> g)
           = (pair z (pair x y) \<circ> (\<otimes>) h) (f \<otimes> g)" for f g h
    by auto
  then have *: "(pair (pair x y) z \<circ> swap \<circ> (\<otimes>) h)
           = (pair z (pair x y) \<circ> (\<otimes>) h)" for h
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_maps_hom pair_hom; simp)+
  have "(pair (pair x y) z) (fg \<otimes> h)
           = (pair z (pair x y)) (h \<otimes> fg)" for fg h
    using *
    using comp_eq_dest_lhs by fastforce
  then show "(pair x y fg) \<circ>\<^sub>d (z h) = (z h) \<circ>\<^sub>d (pair x y fg)" for fg h
    unfolding compatible_def by simp
  show "lvalue z" and  "lvalue (pair x y)"
    by simp_all
qed

lemma compatible_comp_left: "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible (x \<circ> z) y"
  by (simp add: compatible_def lvalue_comp)
  
lemma compatible_comp_inner: 
  "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible (z \<circ> x) (z \<circ> y)"
  by (smt (verit, best) comp_apply compatible_def lvalue_comp lvalue_mult)

subsection \<open>Notation\<close>


bundle lvalue_notation begin
unbundle lvalue_notation
notation tensor_maps_hom (infixr "\<otimes>\<^sub>h" 70)
notation pair ("(_;_)")
end

bundle no_lvalue_notation begin
unbundle lvalue_notation
no_notation tensor_maps_hom (infixr "\<otimes>\<^sub>h" 70)
no_notation pair ("(_;_)")
end
