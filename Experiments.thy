theory Experiments
  imports Finite_Tensor_Product Laws_Quantum Quantum_Extra "HOL-Types_To_Sets.Types_To_Sets"
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)

(* TODO move *)
lemma csubspace_space_as_set[simp]: \<open>csubspace (space_as_set S)\<close>
  by (metis closed_csubspace_def mem_Collect_eq space_as_set)

(* TODO move *)
lemma cdim_UNIV_basis_enum: \<open>cdim (UNIV::'a::basis_enum set) = length (canonical_basis::'a list)\<close>
  apply (subst is_generator_set[symmetric])
  apply (subst complex_vector.dim_span_eq_card_independent)
   apply (rule is_cindependent_set)
  using distinct_canonical_basis distinct_card by blast

(* TODO move *)
lemma cdim_UNIV_ell2: \<open>cdim (UNIV::'a::finite ell2 set) = CARD('a)\<close>
  apply (subst cspan_ket_finite[symmetric])
  apply (subst complex_vector.dim_span_eq_card_independent)
  using cindependent_ket apply blast
  using card_image inj_ket by blast

(* TODO move *)
lemma finite_basis_subspace:
  assumes \<open>csubspace X\<close>
  shows "\<exists>basis::'a::cfinite_dim set. finite basis \<and> cindependent basis \<and> cspan basis = X"
proof -
  from cfinitely_spanned
  obtain S :: \<open>'a set\<close> where \<open>finite S\<close> and \<open>cspan S = UNIV\<close>
    by auto
  from complex_vector.maximal_independent_subset
  obtain B :: \<open>'a set\<close> where \<open>B \<subseteq> X\<close> and \<open>cindependent B\<close> and \<open>X \<subseteq> cspan B\<close>
    by metis
  moreover have \<open>finite B\<close>
    using \<open>cindependent B\<close> cfinitely_spanned complex_vector.independent_span_bound by auto
  moreover have \<open>cspan B \<subseteq> X\<close>
    using \<open>csubspace X\<close> \<open>B \<subseteq> X\<close>
    by (simp add: complex_vector.span_minimal)
  with \<open>X \<subseteq> cspan B\<close> have \<open>cspan B = X\<close>
    by auto
  ultimately show ?thesis
    by auto
qed

(* TODO move *)
lemma surj_isometry_unitary:
  assumes \<open>isometry U\<close>
  assumes \<open>U *\<^sub>S \<top> = \<top>\<close>
  shows \<open>unitary U\<close>
  using assms
  by (metis Proj_I Proj_times idOp_adjoint isometry_def times_idOp1 unitary_def unitary_image)

(* TODO move *)
lemma ortho_isometry:
  assumes spanB: \<open>ccspan B = \<top>\<close>
  assumes orthoU: \<open>\<And>b c. b\<in>B \<Longrightarrow> c\<in>B \<Longrightarrow> cinner (U *\<^sub>V b) (U *\<^sub>V c) = cinner b c\<close>
  shows \<open>isometry U\<close>
proof -
  have [simp]: \<open>b \<in> closure (cspan B)\<close> for b
    using spanB apply transfer by simp
  have *: \<open>cinner (U* *\<^sub>V U *\<^sub>V \<psi>) \<phi> = cinner \<psi> \<phi>\<close> if \<open>\<psi>\<in>B\<close> and \<open>\<phi>\<in>B\<close> for \<psi> \<phi>
    by (simp add: adjoint_I orthoU that(1) that(2))
  have *: \<open>cinner (U* *\<^sub>V U *\<^sub>V \<psi>) \<phi> = cinner \<psi> \<phi>\<close> if \<open>\<psi>\<in>B\<close> for \<psi> \<phi>
    apply (rule equal_span_applyOpSpace[where t=\<phi> and G=B])
    using bounded_clinear_cinner_right *[OF that]
    by auto
  have \<open>U* *\<^sub>V U *\<^sub>V \<phi> = \<phi>\<close> if \<open>\<phi>\<in>B\<close> for \<phi>
    by (simp add: * cinner_extensionality' that)
  then have \<open>U* *\<^sub>V U *\<^sub>V \<phi> = \<phi>\<close> for \<phi>
    by (smt (verit, ccfv_SIG) Bounded_Operators.apply_idOp applyOpSpace_span assms iso_tuple_UNIV_I
              lift_cblinfun_comp(4) top_ccsubspace.rep_eq)
  then have \<open>U* o\<^sub>C\<^sub>L U = idOp\<close>
    by (metis Bounded_Operators.apply_idOp cblinfun_ext lift_cblinfun_comp(4))
  then show \<open>isometry U\<close>
    using isometry_def by blast
qed

typedef ('a::finite,'b::finite) complement_basis = \<open>{..< if CARD('b) div CARD('a) \<noteq> 0 then CARD('b) div CARD('a) else 1}\<close>
  by auto

instance complement_basis :: (finite, finite) finite
proof intro_classes
  have \<open>inj Rep_complement_basis\<close>
    by (simp add: Rep_complement_basis_inject inj_on_def)
  moreover have \<open>finite (range Rep_complement_basis)\<close>
    by (metis finite_lessThan type_definition.Rep_range type_definition_complement_basis)
  ultimately show \<open>finite (UNIV :: ('a,'b) complement_basis set)\<close>
    using Missing_Permutations.inj_on_finite by blast
qed

lemma CARD_complement_basis: 
  assumes \<open>CARD('b::finite) = n * CARD('a::finite)\<close>
  shows \<open>CARD(('a,'b) complement_basis) = n\<close>
proof -
  from assms have \<open>n > 0\<close>
    by (metis zero_less_card_finite zero_less_mult_pos2)
  have *: \<open>inj Rep_complement_basis\<close>
    by (simp add: Rep_complement_basis_inject inj_on_def)
  moreover have \<open>card (range (Rep_complement_basis :: ('a,'b) complement_basis \<Rightarrow> _)) = n\<close>
    apply (subst type_definition.Rep_range[OF type_definition_complement_basis])
    using assms \<open>n > 0\<close> by simp
  ultimately show ?thesis
    by (metis card_image)
qed

(* TODO: closure_is_closed_csubspace[simp] *)

(* TODO: Improve closed_sum_zero_right/left: remove closed A assm, replace rhs by closure A *)

lemma \<open>closure (\<Union>i\<in>I. X) \<supseteq> (\<Union>i\<in>I. closure X)\<close>
  by auto

(* TODO move *)
lemma closed_sum_closure_right[simp]:
  fixes A B :: \<open>'a::real_normed_vector set\<close>
  shows \<open>A +\<^sub>M closure B = A +\<^sub>M B\<close>
proof
  show \<open>A +\<^sub>M B \<subseteq> A +\<^sub>M closure B\<close>
    by (simp add: closed_sum_mono_right closure_subset)
  have \<open>A +\<^sub>M B = closure (\<Union>a\<in>A. plus a ` B)\<close>
    unfolding closed_sum_def set_plus_def
    apply (rule arg_cong[where f=closure]) by auto
  also have \<open>\<dots> = closure (closure (\<Union>a\<in>A. plus a ` B))\<close>
    by simp
  also have \<open>\<dots> \<supseteq> closure (\<Union>a\<in>A. closure (plus a ` B))\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    apply (rule closure_mono)
    by (simp add: Sup_upper UN_least closure_mono)
  also have \<open>\<dots>  = closure (\<Union>a\<in>A. plus a ` closure B)\<close>
    by (simp add: closure_translation)
  also have \<open>\<dots> = A +\<^sub>M closure B\<close>
    unfolding closed_sum_def set_plus_def
    apply (rule arg_cong[where f=closure]) by auto
  finally show \<open>A +\<^sub>M closure B \<subseteq> A +\<^sub>M B\<close>
    by -
qed

lemma closed_sum_closure_left[simp]:
  fixes A B :: \<open>'a::real_normed_vector set\<close>
  shows \<open>closure A +\<^sub>M B = A +\<^sub>M B\<close>
  by (simp add: closed_sum_comm)

lemma closed_sum_cspan[simp]:
  shows \<open>cspan X +\<^sub>M cspan Y = closure (cspan (X \<union> Y))\<close>
  by (smt (verit, best) Collect_cong closed_sum_def complex_vector.span_Un set_plus_def)

lemma norm_to_conjugate_space[simp]: \<open>norm (to_conjugate_space x) = norm x\<close>
  by (fact norm_conjugate_space.abs_eq)

lemma norm_from_conjugate_space[simp]: \<open>norm (from_conjugate_space x) = norm x\<close>
  by (simp add: norm_conjugate_space.rep_eq)

lemma bounded_antilinear_to_conjugate_space[simp]: \<open>bounded_antilinear to_conjugate_space\<close>
  apply (simp add: bounded_antilinear_def bounded_antilinear_axioms_def)
  by (rule exI[of _ 1], simp)


lemma bounded_antilinear_from_conjugate_space[simp]: \<open>bounded_antilinear from_conjugate_space\<close>
  apply (simp add: bounded_antilinear_def bounded_antilinear_axioms_def)
  by (rule exI[of _ 1], simp)

lemma closure_to_conjugate_space: \<open>closure (to_conjugate_space ` X) = to_conjugate_space ` closure X\<close>
proof -
  have 1: \<open>to_conjugate_space ` closure X \<subseteq> closure (to_conjugate_space ` X)\<close>
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  have \<open>\<dots> = to_conjugate_space ` from_conjugate_space ` closure (to_conjugate_space ` X)\<close>
    by (simp add: from_conjugate_space_inverse image_image)
  also have \<open>\<dots> \<subseteq> to_conjugate_space ` closure (from_conjugate_space ` to_conjugate_space ` X)\<close>
    apply (rule image_mono)
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  also have \<open>\<dots> = to_conjugate_space ` closure X\<close>
    by (simp add: to_conjugate_space_inverse image_image)
  finally show ?thesis
    using 1 by simp
qed

lemma closure_from_conjugate_space: \<open>closure (from_conjugate_space ` X) = from_conjugate_space ` closure X\<close>
proof -
  have 1: \<open>from_conjugate_space ` closure X \<subseteq> closure (from_conjugate_space ` X)\<close>
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  have \<open>\<dots> = from_conjugate_space ` to_conjugate_space ` closure (from_conjugate_space ` X)\<close>
    by (simp add: to_conjugate_space_inverse image_image)
  also have \<open>\<dots> \<subseteq> from_conjugate_space ` closure (to_conjugate_space ` from_conjugate_space ` X)\<close>
    apply (rule image_mono)
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  also have \<open>\<dots> = from_conjugate_space ` closure X\<close>
    by (simp add: from_conjugate_space_inverse image_image)
  finally show ?thesis
    using 1 by simp
qed

lemma equal_span_applyOpSpace_antilinear:
  fixes A B :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  assumes \<open>bounded_antilinear A\<close> and \<open>bounded_antilinear B\<close> and
    eq: \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and t: \<open>t \<in> closure (cspan G)\<close>
  shows \<open>A t = B t\<close>
proof -
  have bclA: \<open>bounded_clinear (\<lambda>u. A (from_conjugate_space u))\<close>
    apply (rule bounded_antilinear_o_bounded_antilinear[OF assms(1), unfolded o_def])
    by auto
  have bclB: \<open>bounded_clinear (\<lambda>u. B (from_conjugate_space u))\<close>
    apply (rule bounded_antilinear_o_bounded_antilinear[OF assms(2), unfolded o_def])
    by auto
  have \<open>A (from_conjugate_space u) = B (from_conjugate_space u)\<close> if \<open>u \<in> closure (cspan (to_conjugate_space ` G))\<close> for u
    using bclA bclB _ that apply (rule equal_span_applyOpSpace[where G=\<open>to_conjugate_space ` G\<close>])
    by (metis eq imageE iso_tuple_UNIV_I to_conjugate_space_inverse)
  moreover have \<open>closure (cspan (to_conjugate_space ` G)) = to_conjugate_space ` closure (cspan G)\<close>
    by (simp add: closure_to_conjugate_space)
  ultimately show \<open>A t = B t\<close>
    by (metis imageI iso_tuple_UNIV_I t to_conjugate_space_inverse)
qed

lemma bounded_antilinear_0[simp]: \<open>bounded_antilinear (\<lambda>_. 0)\<close>
  by (rule bounded_antilinear_intro[where K=0], auto)

lemma is_orthogonal_closure_cspan:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> is_orthogonal x y"
  assumes \<open>x \<in> closure (cspan X)\<close> \<open>y \<in> closure (cspan Y)\<close>
  shows "is_orthogonal x y"
proof -
  have *: \<open>cinner x y = 0\<close> if \<open>y \<in> Y\<close> for y
    using bounded_antilinear_cinner_left apply (rule equal_span_applyOpSpace_antilinear[where G=X])
    using assms that by auto
  show \<open>cinner x y = 0\<close>
    using bounded_clinear_cinner_right apply (rule equal_span_applyOpSpace[where G=Y])
    using * assms by auto
qed

(* TODO move *)
lemma Proj_plus:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> is_orthogonal x y"
  shows \<open>Proj (ccspan X) + Proj (ccspan Y) = Proj (ccspan (X \<union> Y))\<close>
proof -
  have \<open>x \<in> cspan X \<Longrightarrow> y \<in> cspan Y \<Longrightarrow> is_orthogonal x y\<close> for x y
    apply (rule is_orthogonal_closure_cspan[where X=X and Y=Y])
    using closure_subset assms by auto
  then have \<open>x \<in> closure (cspan X) \<Longrightarrow> y \<in> closure (cspan Y) \<Longrightarrow> is_orthogonal x y\<close> for x y
    by (metis orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI')
  then show ?thesis
    apply (transfer fixing: X Y)
    apply (subst projection_plus[symmetric])
    by (auto simp add: closure_is_closed_csubspace)
qed

(* TODO move *)
lemma ccspan_leqI:
  assumes \<open>M \<subseteq> space_as_set S\<close>
  shows \<open>ccspan M \<le> S\<close>
  using assms apply transfer
  by (simp add: closed_csubspace.closed closure_minimal complex_vector.span_minimal)

(* TODO move *)
lemma cblinfun_plus_applySpace_distr:
  \<open>(A + B) *\<^sub>S S \<le> A *\<^sub>S S \<squnion> B *\<^sub>S S\<close>
  apply transfer
  by (smt (verit, ccfv_threshold) closed_closure closed_sum_def closure_minimal closure_subset image_subset_iff set_plus_intro subset_eq)

(* TODO move *)
lemma cblinfun_sum_applySpace_distr:
  \<open>(\<Sum>i\<in>I. A i) *\<^sub>S S \<le> (SUP i\<in>I. A i *\<^sub>S S)\<close>
proof (cases \<open>finite I\<close>)
  case True
  then show ?thesis
  proof induction
    case empty
    then show ?case
      by auto
  next
    case (insert x F)
    then show ?case
      using cblinfun_plus_applySpace_distr apply auto
      by (smt (z3) cblinfun_plus_applySpace_distr inf_sup_aci(6) le_iff_sup)
  qed
next
  case False
  then show ?thesis 
    by auto
qed

(* TODO move *)
lemma cblinfun_apply_clinear[simp]: \<open>clinear ((*\<^sub>V) A)\<close>
  using bounded_clinear.axioms(1) cblinfun_apply by blast

(* TODO move  *)
lemma isomorphism_cdim_eqI:
  assumes \<open>clinear f\<close>
  assumes \<open>bij_betw f S T\<close>
  assumes \<open>csubspace S\<close>
  shows \<open>cdim S = cdim T\<close>
proof -
  show ?thesis
    sorry
qed

lemmas cindependent_ket[simp]

(* https://mathoverflow.net/a/390180/101775 *)
lemma register_decomposition:
  fixes \<Phi> :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<exists>U :: ('a \<times> ('a, 'b) complement_basis) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o idOp))\<close>
proof -
  note [[simproc del: compatibility_warn]]
  fix \<xi>0 :: 'a

  have [simp]: \<open>clinear \<Phi>\<close>
    by simp

  define P where \<open>P i = Proj (ccspan {ket i})\<close> for i :: 'a
  have P_butter: \<open>P i = selfbutterket i\<close> for i
    by (simp add: P_def butterfly_proj)

  define P' where \<open>P' i = \<Phi> (P i)\<close> for i :: 'a
  have proj_P': \<open>isProjector (P' i)\<close> for i
    by (simp add: P_def P'_def register_projector)
  have \<open>(\<Sum>i\<in>UNIV. P i) = idOp\<close>
    using sum_butter P_butter by simp
  then have sumP'id: \<open>(\<Sum>i\<in>UNIV. P' i) = idOp\<close>
    unfolding P'_def 
    apply (subst complex_vector.linear_sum[OF \<open>clinear \<Phi>\<close>, symmetric])
    by auto

  define S where \<open>S i = P' i *\<^sub>S \<top>\<close> for i :: 'a
  have P'id: \<open>P' i *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i \<psi>
    using S_def that proj_P'
    by (metis apply_left_neutral isProjector_algebraic)

  obtain B0 where finiteB0: \<open>finite (B0 i)\<close> and cspanB0: \<open>cspan (B0 i) = space_as_set (S i)\<close> for i
  apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    by (metis closed_csubspace_def finite_basis_subspace mem_Collect_eq space_as_set) 

  obtain B where orthoB: \<open>is_ortho_set (B i)\<close>
    and normalB: \<open>\<And>b. b \<in> B i \<Longrightarrow> norm b = 1\<close>
    and cspanB: \<open>cspan (B i) = cspan (B0 i)\<close>
    and finiteB: \<open>finite (B i)\<close> for i
    apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    using orthonormal_basis_of_cspan[OF finiteB0] by blast

  from cspanB cspanB0 have cspanB: \<open>cspan (B i) = space_as_set (S i)\<close> for i
    by simp
  then have ccspanB: \<open>ccspan (B i) = S i\<close> for i
    by (metis ccspan.rep_eq closure_finite_cspan finiteB space_as_set_inject)
  from orthoB have indepB: \<open>cindependent (B i)\<close> for i
    by (simp add: Complex_Inner_Product.is_ortho_set_cindependent)

  have orthoBiBj: \<open>is_orthogonal x y\<close> if \<open>x \<in> B i\<close> and \<open>y \<in> B j\<close> and \<open>i \<noteq> j\<close> for x y i j
  proof -
    from \<open>x \<in> B i\<close> obtain x' where x: \<open>x = P' i *\<^sub>V x'\<close>
      by (metis S_def apply_left_neutral complex_vector.span_base cspanB isProjector_D1 proj_P')
    from \<open>y \<in> B j\<close> obtain y' where y: \<open>y = P' j *\<^sub>V y'\<close>
      by (metis S_def apply_left_neutral complex_vector.span_base cspanB isProjector_D1 proj_P')
    have \<open>cinner x y = cinner (P' i *\<^sub>V x') (P' j *\<^sub>V  y')\<close>
      using x y by simp
    also have \<open>\<dots> = cinner (P' j *\<^sub>V P' i *\<^sub>V x') y'\<close>
      by (metis adjoint_I' isProjector_algebraic proj_P')
    also have \<open>\<dots> = cinner (\<Phi> (P j o\<^sub>C\<^sub>L P i) *\<^sub>V x') y'\<close>
      unfolding P'_def register_mult[OF \<open>register \<Phi>\<close>, symmetric]
      by (simp add: lift_cblinfun_comp(4))
    also have \<open>\<dots> = cinner (\<Phi> (selfbutterket j o\<^sub>C\<^sub>L selfbutterket i) *\<^sub>V x') y'\<close>
      unfolding P_butter by simp
    also have \<open>\<dots> = cinner (\<Phi> 0 *\<^sub>V x') y'\<close>
      by (metis Bounded_Operators.butterfly_times_right Proj_D1 butterfly_0' butterfly_apply butterfly_proj cblinfun_apply_to_zero cinner_zero_right ell2_ket ket_Kronecker_delta_neq that(3))
    also have \<open>\<dots> = 0\<close>
      by (simp add: complex_vector.linear_0)
    finally show ?thesis
      by -
  qed


  define B' where \<open>B' = (\<Union>i\<in>UNIV. B i)\<close>
  
  have P'B: \<open>P' i = Proj (ccspan (B i))\<close> for i
    unfolding ccspanB S_def
    using proj_P' Proj_I isProjector_algebraic by blast

  have \<open>(\<Sum>i\<in>UNIV. P' i) = Proj (ccspan B')\<close>
  proof (unfold B'_def, use finite[of UNIV] in induction)
    case empty
    show ?case by auto
  next
    case (insert j M)
    have \<open>(\<Sum>i\<in>insert j M. P' i) = P' j + (\<Sum>i\<in>M. P' i)\<close>
      by (meson insert.hyps(1) insert.hyps(2) sum.insert)
    also have \<open>\<dots> = Proj (ccspan (B j)) + Proj (ccspan (\<Union>i\<in>M. B i))\<close>
      unfolding P'B insert.IH[symmetric] by simp
    also have \<open>\<dots> = Proj (ccspan (B j \<union> (\<Union>i\<in>M. B i)))\<close>
      apply (rule Proj_plus)
      using orthoBiBj insert.hyps(2) by auto
    also have \<open>\<dots> = Proj (ccspan (\<Union>i\<in>insert j M. B i))\<close>
      by auto
    finally show ?case
      by simp
  qed

  with sumP'id 
  have ccspanB': \<open>ccspan B' = \<top>\<close>
    by (metis applyOpSpace_id imageOp_Proj)
  hence cspanB': \<open>cspan B' = UNIV\<close>
    by (metis B'_def finiteB ccspan.rep_eq finite_UN_I finite_class.finite_UNIV closure_finite_cspan top_ccsubspace.rep_eq)

  from orthoBiBj orthoB have orthoB': \<open>is_ortho_set B'\<close>
    unfolding B'_def is_ortho_set_def by blast
  then have indepB': \<open>cindependent B'\<close>
    using is_ortho_set_cindependent by blast
  have cardB': \<open>card B' = CARD('b)\<close>
    apply (subst complex_vector.dim_span_eq_card_independent[symmetric])
     apply (rule indepB')
    apply (subst cspanB')
    using cdim_UNIV_ell2 by auto

  from orthoBiBj orthoB
  have Bdisj: \<open>B i \<inter> B j = {}\<close> if \<open>i \<noteq> j\<close> for i j
    unfolding is_ortho_set_def
    apply auto by (metis cinner_eq_zero_iff that)

  have cardBsame: \<open>card (B i) = card (B j)\<close> for i j
  proof -
    define Si_to_Sj where \<open>Si_to_Sj i j \<psi> = \<Phi> (butterket j i) *\<^sub>V \<psi>\<close> for i j \<psi>
    have S2S2S: \<open>Si_to_Sj j i (Si_to_Sj i j \<psi>) = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i j \<psi>
      using that P'id
      by (simp add: Si_to_Sj_def times_applyOp[symmetric] register_mult P_butter P'_def)
    also have lin[simp]: \<open>clinear (Si_to_Sj i j)\<close> for i j
      unfolding Si_to_Sj_def by simp
    have S2S: \<open>Si_to_Sj i j x \<in> space_as_set (S j)\<close> for i j x
    proof -
      have \<open>Si_to_Sj i j x = P' j *\<^sub>V Si_to_Sj i j x\<close>
        by (simp add: Si_to_Sj_def times_applyOp[symmetric] register_mult P_butter P'_def)
      also have \<open>P' j *\<^sub>V Si_to_Sj i j x \<in> space_as_set (S j)\<close>
        by (simp add: S_def)
      finally show ?thesis by -
    qed
    have bij: \<open>bij_betw (Si_to_Sj i j) (space_as_set (S i)) (space_as_set (S j))\<close>
      apply (rule bij_betwI[where g=\<open>Si_to_Sj j i\<close>])
      using S2S S2S2S by (auto intro!: funcsetI)
    have \<open>cdim (space_as_set (S i)) = cdim (space_as_set (S j))\<close>
      using lin bij apply (rule isomorphism_cdim_eqI[where f=\<open>Si_to_Sj i j\<close>])
      by simp
    then show ?thesis
      by (metis complex_vector.dim_span_eq_card_independent cspanB indepB)
  qed

  have CARD'b: \<open>CARD('b) = card (B \<xi>0) * CARD('a)\<close>
  proof -
    have \<open>CARD('b) = card B'\<close>
      using cardB' by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. card (B i))\<close>
      unfolding B'_def apply (rule card_UN_disjoint)
      using finiteB Bdisj by auto
    also have \<open>\<dots> = (\<Sum>(i::'a)\<in>UNIV. card (B \<xi>0))\<close>
      using cardBsame by metis
    also have \<open>\<dots> = card (B \<xi>0) * CARD('a)\<close>
      by auto
    finally show ?thesis by -
  qed

  obtain f where bij_f: \<open>bij_betw f (UNIV::('a,'b) complement_basis set) (B \<xi>0)\<close>
    apply atomize_elim apply (rule finite_same_card_bij)
    using finiteB CARD_complement_basis[OF CARD'b] by auto

  define u where \<open>u = (\<lambda>(\<xi>,\<alpha>). \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>)\<close> for \<xi> :: 'a and \<alpha> :: \<open>('a,'b) complement_basis\<close>
  obtain U where Uapply: \<open>U *\<^sub>V ket \<xi>\<alpha> = u \<xi>\<alpha>\<close> for \<xi>\<alpha>
    apply atomize_elim
    apply (rule exI[of _ \<open>cblinfun_extension (range ket) (\<lambda>k. u (inv ket k))\<close>])
    apply (subst cblinfun_extension_exists)
      apply (rule cblinfun_extension_exists_finite)
    by (auto simp add: inj_ket)

  define eqa where \<open>eqa a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: 'a
  define eqc where \<open>eqc a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>('a,'b) complement_basis\<close>
  define eqac where \<open>eqac a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>'a * ('a,'b) complement_basis\<close>

  have \<open>cinner (U *\<^sub>V ket \<xi>\<alpha>) (U *\<^sub>V ket \<xi>'\<alpha>') = eqac \<xi>\<alpha> \<xi>'\<alpha>'\<close> for \<xi>\<alpha> \<xi>'\<alpha>'
  proof -
    obtain \<xi> \<alpha> \<xi>' \<alpha>' where \<xi>\<alpha>: \<open>\<xi>\<alpha> = (\<xi>,\<alpha>)\<close> and \<xi>'\<alpha>': \<open>\<xi>'\<alpha>' = (\<xi>',\<alpha>')\<close>
      apply atomize_elim by auto
    have \<open>cinner (U *\<^sub>V ket (\<xi>,\<alpha>)) (U *\<^sub>V ket (\<xi>', \<alpha>')) = cinner (\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (\<Phi> (butterket \<xi>' \<xi>0) *\<^sub>V f \<alpha>')\<close>
      unfolding Uapply u_def by simp
    also have \<open>\<dots> = cinner ((\<Phi> (butterket \<xi>' \<xi>0))* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: adjoint_I)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>' \<xi>0 *) *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (metis (no_types, lifting) assms register_def)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>0 \<xi>' o\<^sub>C\<^sub>L butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: register_mult times_applyOp[symmetric])
    also have \<open>\<dots> = cinner (\<Phi> (eqa \<xi>' \<xi> *\<^sub>C selfbutterket \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      apply simp
      by (metis eqa_def ket_Kronecker_delta_eq ket_is_orthogonal)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (\<Phi> (selfbutterket \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (smt (verit, ccfv_threshold) \<open>clinear \<Phi>\<close> eqa_def applyOp_scaleC1 cinner_commute 
              cinner_scaleC_left cinner_zero_right complex_cnj_one complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (P' \<xi>0 *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      using P_butter P'_def by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (f \<alpha>) (f \<alpha>')\<close>
      apply (subst P'id)
       apply (metis bij_betw_imp_surj_on bij_f complex_vector.span_base cspanB rangeI)
      by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * eqc \<alpha> \<alpha>'\<close>
      using bij_f orthoB normalB unfolding is_ortho_set_def eqc_def apply auto
      apply (metis bij_betw_imp_surj_on cnorm_eq_1 rangeI)
      by (smt (z3) bij_betw_iff_bijections iso_tuple_UNIV_I)
    finally show ?thesis
      by (simp add: eqa_def eqac_def eqc_def \<xi>'\<alpha>' \<xi>\<alpha>)
  qed
  then have \<open>isometry U\<close>
    apply (rule_tac ortho_isometry[where B=\<open>range ket\<close>])
    using eqac_def by auto

  have \<open>U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U = butterket \<xi> \<eta> \<otimes>\<^sub>o idOp\<close> for \<xi> \<eta>
  proof (rule equal_ket, rename_tac \<xi>1\<alpha>)
    fix \<xi>1\<alpha> obtain \<xi>1 :: 'a and \<alpha> :: \<open>('a,'b) complement_basis\<close> where \<xi>1\<alpha>: \<open>\<xi>1\<alpha> = (\<xi>1,\<alpha>)\<close> 
      apply atomize_elim by auto
    have \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta>) *\<^sub>V \<Phi> (butterket \<xi>1 \<xi>0) *\<^sub>V f \<alpha>\<close>
      unfolding times_applyOp \<xi>1\<alpha> Uapply u_def by simp
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta> o\<^sub>C\<^sub>L butterket \<xi>1 \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (simp add: lift_cblinfun_comp(4) register_mult)
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (eqa \<eta> \<xi>1 *\<^sub>C butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (simp add: eqa_def ket_Kronecker_delta)
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (simp add: complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V U *\<^sub>V ket (\<xi>, \<alpha>)\<close>
      unfolding Uapply u_def by simp
    also from \<open>isometry U\<close> have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C ket (\<xi>, \<alpha>)\<close>
      unfolding times_applyOp[symmetric] by simp
    also have \<open>\<dots> = (butterket \<xi> \<eta> *\<^sub>V ket \<xi>1) \<otimes>\<^sub>s ket \<alpha>\<close>
      by (simp add: eqa_def tensor_ell2_scaleC1)
    also have \<open>\<dots> = (butterket \<xi> \<eta> \<otimes>\<^sub>o idOp) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by (simp add: \<xi>1\<alpha> tensor_op_ket)
    finally show \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = (butterket \<xi> \<eta> \<otimes>\<^sub>o idOp) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by -
  qed
  then have 1: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o idOp\<close> for \<theta>
    apply (rule_tac clinear_eq_butterketI[THEN fun_cong, where x=\<theta>])
    by (auto intro!: clinearI simp add: cblinfun_apply_dist1 complex_vector.linear_add complex_vector.linear_scale)

  have \<open>unitary U\<close>
  proof -
    have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close> for \<xi> \<xi>1
    proof -
      have *: \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b \<in> space_as_set (U *\<^sub>S \<top>)\<close> if \<open>b \<in> B \<xi>0\<close> for b
        apply (subst asm_rl[of \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b = u (\<xi>, inv f b)\<close>])
         apply (simp add: u_def, metis bij_betw_inv_into_right bij_f that)
        by (metis Uapply cblinfun_apply_in_image)

      have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>1) *\<^sub>S \<top>\<close>
        unfolding cblinfun_apply_assoc_subspace[symmetric] register_mult[OF assms]
        by simp
      also have \<open>\<dots> \<le> \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<top>\<close>
        by (meson applyOpSpace_mono top_greatest)
      also have \<open>\<dots> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S S \<xi>0\<close>
        by (simp add: S_def P'_def P_butter)
      also have \<open>\<dots> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S ccspan (B \<xi>0)\<close>
        by (simp add: ccspanB)
      also have \<open>\<dots> = ccspan (\<Phi> (butterket \<xi> \<xi>0) ` B \<xi>0)\<close>
        by (rule applyOpSpace_Span)
      also have \<open>\<dots> \<le> U *\<^sub>S \<top>\<close>
        by (rule ccspan_leqI, use * in auto)
      finally show ?thesis by -
    qed
    moreover have \<open>\<Phi> idOp *\<^sub>S \<top> \<le> (SUP \<xi>\<in>UNIV. \<Phi> (selfbutterket \<xi>) *\<^sub>S \<top>)\<close>
      unfolding sum_butter[symmetric]
      apply (subst complex_vector.linear_sum, simp)
      by (rule cblinfun_sum_applySpace_distr)
    ultimately have \<open>\<Phi> idOp *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close>
      apply auto by (meson SUP_le_iff order.trans)
    then have \<open>U *\<^sub>S \<top> = \<top>\<close>
      apply auto
      using top.extremum_unique by blast
    with \<open>isometry U\<close> show \<open>unitary U\<close>
      by (rule surj_isometry_unitary)
  qed

  have \<open>\<Phi> \<theta> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o idOp) o\<^sub>C\<^sub>L U*\<close> for \<theta>
  proof -
    from \<open>unitary U\<close>
    have \<open>\<Phi> \<theta> = (U o\<^sub>C\<^sub>L U*) o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L U*)\<close>
      by simp
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (U*  o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L U*\<close>
      by (simp add: assoc_left(1))
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o idOp) o\<^sub>C\<^sub>L U*\<close>
      using 1 by simp
    finally show ?thesis
      by -
  qed

  with \<open>unitary U\<close> show ?thesis
    by (auto simp: sandwich_def)
qed

lemma register_decomposition_converse: 
  assumes \<open>unitary U\<close>
  shows \<open>register (\<lambda>x. sandwich U (idOp \<otimes>\<^sub>o x))\<close>
  using _ unitary_sandwich_register apply (rule register_comp[unfolded o_def])
  using assms by auto

lemma idOp_not_0[simp]: \<open>(idOp :: 'a::{complex_normed_vector, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _) \<noteq> 0\<close>
  by (metis ccsubspace_top_not_bot kernel_0 kernel_id zero_ccsubspace_def)

lemma tensor_ell2_nonzero: \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close> if \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  apply (use that in transfer)
  apply auto
  by (metis mult_eq_0_iff old.prod.case)

lemma tensor_op_nonzero:
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  assumes \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  shows \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>a *\<^sub>V ket i \<noteq> 0\<close>
    by (metis applyOp0 equal_ket)
  from \<open>b \<noteq> 0\<close> obtain j where j: \<open>b *\<^sub>V ket j \<noteq> 0\<close>
    by (metis applyOp0 equal_ket)
  from i j have ijneq0: \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  have \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) = (a \<otimes>\<^sub>o b) *\<^sub>V ket (i,j)\<close>
    by (simp add: tensor_op_ket)
  with ijneq0 show \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by force
qed

lemma inj_tensor_left: \<open>inj (\<lambda>a::'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2. a \<otimes>\<^sub>o b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>o b = y \<otimes>\<^sub>o b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>x \<otimes>\<^sub>o b \<noteq> y \<otimes>\<^sub>o b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_left_add) 
  with eq show False
    by auto
qed

lemma register_inj: \<open>inj F\<close> if \<open>register F\<close>
proof -
  obtain U :: \<open>('a \<times> ('a, 'b) complement_basis) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where \<open>unitary U\<close> and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o idOp)\<close> for a
    apply atomize_elim using \<open>register F\<close> by (rule register_decomposition)
  have \<open>inj (sandwich U)\<close>
    by (smt (verit, best) \<open>unitary U\<close> assoc_left(1) inj_onI sandwich_def times_idOp1 times_idOp2 unitary_def)
  moreover have \<open>inj (\<lambda>a::'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _. a \<otimes>\<^sub>o idOp)\<close>
    by (rule inj_tensor_left, simp)
  ultimately show \<open>inj F\<close>
    unfolding F
    by (smt (z3) inj_def) 
qed

lemma swap_swap: \<open>swap o swap = id\<close>
  by (metis Laws_Quantum.swap_def compatible_Snd_Fst pair_Fst_Snd pair_o_swap)

definition \<open>iso_register F \<longleftrightarrow> register F \<and> (\<exists>G. register G \<and> F o G = id \<and> G o F = id)\<close>

lemma iso_registerI:
  assumes \<open>register F\<close> \<open>register G\<close> \<open>F o G = id\<close> \<open>G o F = id\<close>
  shows \<open>iso_register F\<close>
  using assms(1) assms(2) assms(3) assms(4) iso_register_def by blast

(* definition \<open>equivalent_registers F G \<longleftrightarrow> (register F \<and> (\<exists>I. iso_register I \<and> F o I = G))\<close>

lemma equivalent_registers_sym:
  assumes \<open>equivalent_registers F G\<close>
  shows \<open>equivalent_registers G F\<close>
   *)

definition \<open>complements F G \<longleftrightarrow> compatible F G \<and> iso_register (F;G)\<close>

lemma complements_sym: \<open>complements G F\<close> if \<open>complements F G\<close>
proof -
  from that have \<open>iso_register (F;G)\<close>
    by (meson complements_def)
  then obtain I where [simp]: \<open>register I\<close> and \<open>(F;G) o I = id\<close> and \<open>I o (F;G) = id\<close>
    using iso_register_def by blast
(*   from \<open>iso_register I\<close> obtain I'
    where II'[simp]: \<open>I o I' = id\<close> and I'I[simp]: \<open>I' o I = id\<close> and [simp]: \<open>register I'\<close>
    using iso_register_def by blastx *)
  have \<open>register (swap o I)\<close>
    using \<open>register I\<close> register_comp register_swap by blast
(*   have \<open>iso_register (swap o I)\<close>
    apply (rule iso_registerI[where G=\<open>I' o swap\<close>])
       apply auto[2]
    using II'[THEN fun_cong] I'I swap_swap[where 'a='c and 'b='a, THEN fun_cong]
      swap_swap[where 'a='a and 'b='c, THEN fun_cong]
    by (simp_all add: o_def id_def) *)
  moreover have \<open>(G;F) o (swap o I) = id\<close>
    by (metis (no_types, hide_lams) \<open>(F;G) \<circ> I = id\<close> compatible_def complements_def pair_o_swap rewriteL_comp_comp that)
  moreover have \<open>(swap o I) o (G;F) = id\<close>
    by (metis (no_types, hide_lams) Experiments.swap_swap \<open>I \<circ> (F;G) = id\<close> calculation(2) comp_def eq_id_iff)
  ultimately have \<open>iso_register (G;F)\<close>
    using compatible_sym complements_def iso_registerI pair_is_register that by blast
  then show \<open>complements G F\<close>
    by (meson compatible_sym complements_def that)
qed

lemma complement_exists:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes \<open>register F\<close>
  shows \<open>\<exists>G :: ('a, 'b) complement_basis update \<Rightarrow> 'b update. complements F G\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  obtain U :: \<open>('a \<times> ('a, 'b) complement_basis) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o idOp)\<close> for a
    apply atomize_elim using assms by (rule register_decomposition)
  define G :: \<open>(('a, 'b) complement_basis) update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (idOp \<otimes>\<^sub>o b)\<close> for b
  have [simp]: \<open>register G\<close>
    unfolding G_def apply (rule register_decomposition_converse) by simp
  have \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close> for a b
  proof -
    have \<open>F a o\<^sub>C\<^sub>L G b = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> adjUU assoc_left(1) comp_tensor_op times_idOp1 times_idOp2 unitary_isometry)
    moreover have \<open>G b o\<^sub>C\<^sub>L F a = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> adjUU assoc_left(1) comp_tensor_op times_idOp1 times_idOp2 unitary_isometry)
    ultimately show ?thesis by simp
  qed
  then have [simp]: \<open>compatible F G\<close>
    by (auto simp: compatible_def \<open>register F\<close> \<open>register G\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      apply (auto simp: register_pair_apply F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> adjUU assoc_left(1) comp_tensor_op times_idOp1 times_idOp2 unitary_isometry)
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)
    define I where \<open>I = sandwich (U*)\<close> for x
    have [simp]: \<open>register I\<close>
      by (simp add: I_def unitary_sandwich_register)
    have \<open>I o (F;G) = id\<close> and FGI: \<open>(F;G) o I = id\<close>
      apply (auto intro!:ext simp: I_def[abs_def] FG sandwich_def)
      apply (metis (no_types, hide_lams) \<open>unitary U\<close> adjUU assoc_left(1) times_idOp1 times_idOp2 unitary_isometry)
      by (metis (no_types, lifting) UadjU \<open>unitary U\<close> assoc_left(1) times_idOp1 times_idOp2)
    then show \<open>iso_register (F;G)\<close>
      by (auto intro!: iso_registerI)
  qed
  ultimately show ?thesis
    apply (rule_tac exI[of _ G]) by (auto simp: complements_def)
qed

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

lemma commutant_exchange:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes \<open>iso_register F\<close>
  shows \<open>commutant (F ` X) = F ` commutant X\<close>
proof (rule Set.set_eqI)
  fix x :: \<open>'b update\<close>
  from assms
  obtain G where \<open>F o G = id\<close> and \<open>G o F = id\<close> and [simp]: \<open>register G\<close>
    using iso_register_def by blast
  from assms have [simp]: \<open>register F\<close>
    using iso_register_def by blast
  have \<open>x \<in> commutant (F ` X) \<longleftrightarrow> (\<forall>y \<in> F ` X. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> F ` X. G x o\<^sub>C\<^sub>L G y = G y o\<^sub>C\<^sub>L G x)\<close>
    by (metis (no_types, hide_lams) \<open>F \<circ> G = id\<close> \<open>G o F = id\<close> \<open>register G\<close> comp_def eq_id_iff register_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> X. G x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L G x)\<close>
    by (simp add: \<open>G \<circ> F = id\<close> pointfree_idE)
  also have \<open>\<dots> \<longleftrightarrow> G x \<in> commutant X\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by (metis (no_types, hide_lams) \<open>G \<circ> F = id\<close> \<open>F \<circ> G = id\<close> image_iff pointfree_idE)
  finally show \<open>x \<in> commutant (F ` X) \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by -
qed

lemma commutant_tensor1: \<open>commutant (range (\<lambda>a. a \<otimes>\<^sub>o idOp)) = range (\<lambda>b. idOp \<otimes>\<^sub>o b)\<close>
  sorry

lemma complement_range:
  assumes \<open>complements F G\<close>
  shows \<open>range G = commutant (range F)\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms compatible_def complements_def by metis+
  have [simp]: \<open>iso_register (F;G)\<close>
    using assms complements_def by blast
  have [simp]: \<open>(F;G) (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close> for a b
    using Laws_Quantum.register_pair_apply assms complements_def by blast
  have [simp]: \<open>range F = (F;G) ` range (\<lambda>a. a \<otimes>\<^sub>o idOp)\<close>
    by force
  have [simp]: \<open>range G = (F;G) ` range (\<lambda>b. idOp \<otimes>\<^sub>o b)\<close>
    by force
  show \<open>range G = commutant (range F)\<close>
    by (simp add: commutant_exchange commutant_tensor1)
qed

(* (* TODO not used? *)
lemma register_isometric: \<open>norm (F x) = norm x\<close> if \<open>register F\<close>
   *)

lemma register_adjoint: "F (a*) = (F a)*" if \<open>register F\<close>
  using register_def that by blast

lemma same_range_equivalent:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'c::finite update\<close> and G :: \<open>'b::finite update \<Rightarrow> 'c::finite update\<close>
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes \<open>range F = range G\<close>
  shows \<open>\<exists>I. iso_register I \<and> F o I = G\<close>
proof -
  have G_rangeF[simp]: \<open>G x \<in> range F\<close> for x
    by (simp add: assms)
  have F_rangeG[simp]: \<open>F x \<in> range G\<close> for x
    by (simp add: assms(3)[symmetric])
  have [simp]: \<open>inj F\<close> and [simp]: \<open>inj G\<close>
    by (simp_all add: register_inj)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    by simp_all
  define I J where \<open>I x = inv F (G x)\<close> and \<open>J y = inv G (F y)\<close> for x y
  have addI: \<open>I (x + y) = I x + I y\<close> for x y
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_add)
  have addJ: \<open>J (x + y) = J x + J y\<close> for x y
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_add)
  have scaleI: \<open>I (r *\<^sub>C x) = r *\<^sub>C I x\<close> for r x
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_scale)
  have scaleJ: \<open>J (r *\<^sub>C x) = r *\<^sub>C J x\<close> for r x
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_scale)
(*  have norm: \<open>norm (I x) = norm x\<close> for x
  proof -
    have \<open>norm (I x) = norm (F (I x))\<close>
      by (simp add: register_isometric)
    also have \<open>\<dots> = norm (G x)\<close>
    also have \<open>\<dots> = norm x\<close>
      by (simp add: register_isometric)
    finally show ?thesis by -
  qed *)
  have unitalI: \<open>I idOp = idOp\<close>
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F])
     apply auto
    by (metis Axioms_Quantum.register_id G_rangeF assms(2))
  have unitalJ: \<open>J idOp = idOp\<close>
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G])
     apply auto
    by (metis Axioms_Quantum.register_id F_rangeG assms(1))
  have multI: \<open>I (a o\<^sub>C\<^sub>L b) = I a o\<^sub>C\<^sub>L I b\<close> for a b
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_mult[symmetric, OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: register_mult)
  have multJ: \<open>J (a o\<^sub>C\<^sub>L b) = J a o\<^sub>C\<^sub>L J b\<close> for a b
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_mult[symmetric, OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: register_mult)
  have adjI: \<open>I (a*) = (I a)*\<close> for a
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_adjoint[OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    using assms(2) register_adjoint by blast
  have adjJ: \<open>J (a*) = (J a)*\<close> for a
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_adjoint[OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    using assms(1) register_adjoint by blast

  from addI scaleI unitalI multI adjI
  have \<open>register I\<close>
    unfolding register_def by (auto intro!: clinearI)
  from addJ scaleJ unitalJ multJ adjJ
  have \<open>register J\<close>
    unfolding register_def by (auto intro!: clinearI)

  have \<open>I o J = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj F\<close>])
    by auto
  have \<open>J o I = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj G\<close>])
    by auto

  from \<open>I o J = id\<close> \<open>J o I = id\<close> \<open>register I\<close> \<open>register J\<close>
  have \<open>iso_register I\<close>
    using iso_register_def by blast

  have \<open>F o I = G\<close>
    unfolding I_def o_def
    by (subst Hilbert_Choice.f_inv_into_f[where f=F], auto)

  with \<open>iso_register I\<close> show ?thesis
    by auto
qed

lemma iso_register_id[simp]: \<open>iso_register id\<close>
  by (simp add: iso_register_def)

lemma tensor_register_distrib: \<open>(F \<otimes>\<^sub>r G) o (F' \<otimes>\<^sub>r G') = (F o F') \<otimes>\<^sub>r (G o G')\<close> 
  if [simp]: \<open>register F\<close> \<open>register G\<close> \<open>register F'\<close> \<open>register G'\<close>
  apply (rule tensor_extensionality)
  by (auto simp: register_tensor_is_hom)

lemma register_tensor_id[simp]: \<open>id \<otimes>\<^sub>r id = id\<close>
  apply (rule tensor_extensionality)
  by (auto simp add: register_tensor_is_hom)

lemma iso_register_tensor[simp]: \<open>iso_register (F \<otimes>\<^sub>r G)\<close> if \<open>iso_register F\<close> and \<open>iso_register G\<close>
proof -
  from that have [simp]: \<open>register F\<close> \<open>register G\<close>
    using iso_register_def by blast+
  from \<open>iso_register F\<close>
  obtain F' where [simp]: \<open>register F'\<close> \<open>F o F' = id\<close> \<open>F' o F = id\<close>
    using iso_register_def by blast
  from \<open>iso_register G\<close>
  obtain G' where [simp]: \<open>register G'\<close> \<open>G o G' = id\<close> \<open>G' o G = id\<close>
    using iso_register_def by blast
  show ?thesis
    apply (rule iso_registerI[where G=\<open>F' \<otimes>\<^sub>r G'\<close>])
    by (auto simp add: register_tensor_is_hom tensor_register_distrib)
qed

(* I think the only quantum specific step here so far is the use of commutant_tensor1 and same_range_equivalent *)
lemma complement_unique:
  assumes "complements F G"
  assumes "complements F H"
  shows "\<exists>I. iso_register I \<and> (F;G) o I = (F;H)"
proof -
  from assms
  have \<open>range G = range H\<close>
    by (metis complement_range)
  then obtain J where [simp]: \<open>iso_register J\<close> and \<open>G o J = H\<close>
    by (meson assms(1) assms(2) compatible_def complements_def same_range_equivalent)
(*   have \<open>((F;G) o (id \<otimes>\<^sub>r J)) (idOp \<otimes>\<^sub>o b) = (F;H) (idOp \<otimes>\<^sub>o b)\<close> for b
    by (metis \<open>G \<circ> J = H\<close> \<open>iso_register J\<close> assms(1) comp_id complements_def iso_register_def pair_o_tensor register_id')
  moreover have \<open>((F;G) o (id \<otimes>\<^sub>r J)) (a \<otimes>\<^sub>o idOp) = (F;H) (a \<otimes>\<^sub>o idOp)\<close> for a
    by (metis \<open>G \<circ> J = H\<close> \<open>iso_register J\<close> assms(1) comp_id complements_def iso_register_def pair_o_tensor register_id')
  ultimately *)
  (* have \<open>((F;G) o (id \<otimes>\<^sub>r J)) (a \<otimes>\<^sub>o b) = (F;H) (a \<otimes>\<^sub>o b)\<close> for a b
    by (metis \<open>G \<circ> J = H\<close> \<open>iso_register J\<close> assms(1) comp_id complements_def iso_register_def pair_o_tensor register_id')
  then *) have \<open>(F;G) o (id \<otimes>\<^sub>r J) = (F;H)\<close>
    by (metis \<open>G \<circ> J = H\<close> \<open>iso_register J\<close> assms(1) comp_id complements_def iso_register_def pair_o_tensor register_id')
  moreover have \<open>iso_register (id \<otimes>\<^sub>r J)\<close>
    by simp
  ultimately show ?thesis
    by blast
qed

end
