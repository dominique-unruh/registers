theory Experiments
  imports Finite_Tensor_Product Laws_Quantum Quantum_Extra "HOL-Types_To_Sets.Types_To_Sets"
begin

no_notation m_inv ("inv\<index> _" [81] 80)

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


(* TODO move *)
lemma ccspan_leqI:
  assumes \<open>M \<subseteq> space_as_set S\<close>
  shows \<open>ccspan M \<le> S\<close>
  using assms apply transfer
  by (simp add: closed_csubspace.closed closure_minimal complex_vector.span_minimal)


(* https://mathoverflow.net/a/390180/101775 *)
lemma
  fixes \<Phi> :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<exists>U :: ('a \<times> ('a, 'b) complement_basis) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o idOp) o\<^sub>C\<^sub>L U*)\<close>
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

  obtain B0 where finiteB0: \<open>finite (B0 i)\<close> and cspanB0: \<open>cspan (B0 i) = space_as_set (S i)\<close> for i
  apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    by (metis closed_csubspace_def finite_basis_subspace mem_Collect_eq space_as_set) 

  obtain B where orthoB: \<open>is_ortho_set (B i)\<close>  and 
      cspanB: \<open>cspan (B i) = cspan (B0 i)\<close>
    and finiteB: \<open>finite (B i)\<close> for i
    apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    apply (rule allI)
    using finiteB0 by (rule orthogonal_basis_of_cspan)

  from cspanB cspanB0 have cspanB: \<open>cspan (B i) = space_as_set (S i)\<close> for i
    by simp
  then have ccspanB: \<open>ccspan (B i) = S i\<close> for i
    by (metis ccspan.rep_eq closure_finite_cspan finiteB space_as_set_inject)
  from orthoB have indepB: \<open>cindependent (B i)\<close> for i
    by (simp add: Complex_Inner_Product.is_ortho_set_cindependent)

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
      sorry (* TODO: add corresponding law in BO first *)
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

  have orthoBiBj: \<open>is_orthogonal x y\<close> if \<open>x \<in> B i\<close> and \<open>y \<in> B j\<close> and \<open>i \<noteq> j\<close> for x y i j
    sorry
  with orthoB have orthoB': \<open>is_ortho_set B'\<close>
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

  have \<open>cdim (space_as_set (S i)) = cdim (space_as_set (S j))\<close> for i j
    sorry
  then have cardBsame: \<open>card (B i) = card (B j)\<close> for i j
    by (metis complex_vector.dim_span_eq_card_independent cspanB indepB)

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
    sorry

  define eqa where \<open>eqa a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: 'a
  define eqc where \<open>eqc a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>('a,'b) complement_basis\<close>
  define eqac where \<open>eqac a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>'a * ('a,'b) complement_basis\<close>

  have \<open>cinner (U *\<^sub>V ket (\<xi>,\<alpha>)) (U *\<^sub>V ket (\<xi>', \<alpha>')) = eqac (\<xi>,\<alpha>) (\<xi>',\<alpha>')\<close> for \<xi> \<alpha> \<xi>' \<alpha>'
  proof -
    have \<open>cinner (U *\<^sub>V ket (\<xi>,\<alpha>)) (U *\<^sub>V ket (\<xi>', \<alpha>')) = cinner (\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (\<Phi> (butterket \<xi>' \<xi>0) *\<^sub>V f \<alpha>')\<close>
      unfolding Uapply u_def by simp
    also have \<open>\<dots> = cinner ((\<Phi> (butterket \<xi>' \<xi>0))* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: adjoint_I)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>' \<xi>0 *) *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (metis (no_types, lifting) assms register_def)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>0 \<xi>' o\<^sub>C\<^sub>L butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (metis (no_types, lifting) adjoint_twice assms butterfly_def' register_mult times_adjoint times_applyOp)
    also have \<open>\<dots> = cinner (\<Phi> (eqa \<xi>' \<xi> *\<^sub>C selfbutterket \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      unfolding butterfly_def' 
      apply (subst cblinfun_apply_assoc[symmetric])
      apply (subst cblinfun_apply_assoc)
      apply simp
      by (metis eqa_def ket_Kronecker_delta_eq ket_is_orthogonal)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (\<Phi> (selfbutterket \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (smt (verit, ccfv_threshold) \<open>clinear \<Phi>\<close> eqa_def applyOp_scaleC1 cinner_commute 
              cinner_scaleC_left cinner_zero_right complex_cnj_one complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (P' \<xi>0 *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      using P_butter P'_def by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (f \<alpha>) (f \<alpha>')\<close>
      sorry
    also have \<open>\<dots> = eqa \<xi>' \<xi> * eqc \<alpha> \<alpha>'\<close>
      sorry
    finally show ?thesis
      by (simp add: eqa_def eqac_def eqc_def)
  qed
  then have \<open>isometry U\<close>
    sorry


  have \<open>U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U = butterket \<xi> \<eta> \<otimes>\<^sub>o idOp\<close> for \<xi> \<eta>
  proof (rule equal_ket, rename_tac \<xi>1\<alpha>)
    fix \<xi>1\<alpha> obtain \<xi>1 :: 'a and \<alpha> :: \<open>('a,'b) complement_basis\<close> where \<xi>1\<alpha>: \<open>\<xi>1\<alpha> = (\<xi>1,\<alpha>)\<close> 
      apply atomize_elim by auto
    have \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta>) *\<^sub>V \<Phi> (butterket \<xi>1 \<xi>0) *\<^sub>V f \<alpha>\<close>
      unfolding times_applyOp \<xi>1\<alpha> Uapply u_def by simp
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta> o\<^sub>C\<^sub>L butterket \<xi>1 \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (simp add: lift_cblinfun_comp(4) register_mult)
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (eqa \<eta> \<xi>1 *\<^sub>C butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>\<close>
      sorry
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>\<close>
      sorry
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V U *\<^sub>V ket (\<xi>, \<alpha>)\<close>
      unfolding Uapply u_def by simp
    also from \<open>isometry U\<close> have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C ket (\<xi>, \<alpha>)\<close>
      unfolding times_applyOp[symmetric] by simp
    also have \<open>\<dots> = (butterket \<xi> \<eta> *\<^sub>V ket \<xi>1) \<otimes>\<^sub>s ket \<alpha>\<close>
      by (simp add: butterfly_apply eqa_def tensor_ell2_scaleC1)
    also have \<open>\<dots> = (butterket \<xi> \<eta> \<otimes>\<^sub>o idOp) *\<^sub>V ket \<xi>1\<alpha>\<close>
      sorry
    finally show \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = (butterket \<xi> \<eta> \<otimes>\<^sub>o idOp) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by -
  qed
  then have 1: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o idOp\<close> for \<theta>
    sorry

  have \<open>unitary U\<close>
  proof -
    have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close> for \<xi> \<xi>1
    proof -
      have *: \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b \<in> space_as_set (U *\<^sub>S \<top>)\<close> if \<open>b \<in> B \<xi>0\<close> for b
        apply (subst asm_rl[of \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b = u (\<xi>, inv f b)\<close>])
         apply (simp add: u_def, metis bij_betw_inv_into_right bij_f that)
        by (metis Uapply cblinfun_apply_in_image)

      have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>1) *\<^sub>S \<top>\<close>
        unfolding cblinfun_apply_assoc_subspace[symmetric] register_mult[OF assms] butterfly_def'
        apply (subst (2) cblinfun_apply_assoc[symmetric]) apply (subst (2) cblinfun_apply_assoc)
        apply simp
        apply (subst cblinfun_apply_assoc[symmetric]) apply (subst cblinfun_apply_assoc)
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
    then have \<open>\<Phi> idOp *\<^sub>V \<alpha> \<in> space_as_set (U *\<^sub>S \<top>)\<close> for \<alpha>
      sorry
    then have \<open>space_as_set (U *\<^sub>S \<top>) = UNIV\<close>
      by auto
    with \<open>isometry U\<close> show \<open>unitary U\<close>
      by (metis Proj_I Proj_times isometry_def range_adjoint_isometry space_as_set_inject times_idOp1 top_ccsubspace.rep_eq unitary_def unitary_id)
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
    by auto
qed



end
