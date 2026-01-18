theory Deterministic_Aux
  imports Language
begin
lemma exec_det_aux: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow> \<sigma>'' = \<sigma>'"
proof (induction arbitrary: \<sigma>'' rule: exec.induct)
  case (exec_method_call \<phi> x y m params stmts a \<chi> C paramValues M meth \<phi>'' \<psi>)
  from \<open>M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close> 
  show ?case
    apply(rule exec.cases) 
    using exec_method_call
    by auto
next
  case (exec_var_assign \<phi> x y stmts M \<psi> \<chi>)
  from \<open>M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close> 
  show ?case
    apply (rule exec.cases) 
    by (auto simp: exec_var_assign)   
next
  case (exec_field_assign \<phi> y x stmts v \<chi> \<chi>' M \<psi>)
  from \<open>M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>  
  show ?case
    apply (rule exec.cases) 
    using  exec_field_assign 
    by auto    
next
  case (exec_new \<phi> x C params stmts paramValues M c obj' a \<chi> \<chi>' \<psi>)
  from \<open>M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close> 
  show ?case 
    apply (rule exec.cases) 
    using exec_new 
    by auto
next
  case (exec_return \<phi> x stmts \<phi>' x' stmts' M \<psi> \<chi>)
  from \<open>M, (\<phi> # \<phi>' # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>
  show ?case 
    apply (rule exec.cases) 
    using exec_return 
    by auto
qed

lemma internal_exec_rev_tr_nonempty':
  "internal_exec_rev M M' \<sigma> tr \<sigma>' \<Longrightarrow> tr = [] \<Longrightarrow> False"

  apply(induction rule: internal_exec_rev.induct, auto)
  done

lemma internal_exec_rev_tr_nonempty:
  "internal_exec_rev M M' \<sigma> [] \<sigma>' \<Longrightarrow> False"
  using internal_exec_rev_tr_nonempty' 
  by blast

lemma internal_exec_rev'_appI:
  "internal_exec_rev' M M' \<sigma> tr \<sigma>' \<Longrightarrow>
  internal_exec_rev' M M' \<sigma>' tr' \<sigma>'' \<Longrightarrow>
  internal_exec_rev' M M' \<sigma> (tr @ tr') \<sigma>''"

  apply(induct rule: internal_exec_rev'.induct)
  using internal_step 
  by auto

lemma internal_exec_rev_appI:
  assumes "internal_exec_rev M M' \<sigma> tr \<sigma>'''"
  assumes "internal_exec_rev' M M' \<sigma>''' tr' \<sigma>''"
  shows "internal_exec_rev M M' \<sigma> (tr @ tr') \<sigma>''"

  using assms 
  apply(induction tr arbitrary: \<sigma> \<sigma>''' tr' \<sigma>'')
  using internal_exec_rev_tr_nonempty 
   apply blast
  apply(erule internal_exec_rev.cases)
  by (simp add: internal_exec_rev'_appI internal_exec_rev_first_step)  

lemma trace_rev1: 
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow> internal_exec_rev M M' \<sigma> tr \<sigma>'"
proof  (induction rule: internal_exec.induct)
  case (internal_exec_first_step \<sigma> \<sigma>' c c')
  thus ?case
    by (simp add: internal_exec_rev_first_step internal_refl)
next 
   case (internal_exec_more_steps \<sigma> tr \<sigma>' \<sigma>'' c)  
   note facts = internal_exec_more_steps
   thus ?case
   proof (cases rule: internal_exec.cases)
     case (internal_exec_first_step c c')
     thus ?thesis 
       using facts internal_exec_rev_first_step internal_refl internal_step 
       by auto
   next
     case (internal_exec_more_steps tr' \<sigma>''' c')
     thus ?thesis 
       using internal_exec_rev_appI facts internal_refl internal_step 
       by blast
   qed
qed

lemma internal_exec_tr_nonempty:
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow> tr = [] \<Longrightarrow> False"

  by(induct rule: internal_exec.induct, auto)

lemma internal_exec_tr_nonempty' [simp]:
  "internal_exec M M' \<sigma> [] \<sigma>' = False"

  using internal_exec_tr_nonempty 
  by blast
(*internal_exec_rev' (the second premise) *)
lemma internal_exec_appI:  
  assumes "internal_exec_rev' M M' \<sigma>' tr \<sigma>''"
          "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> \<sigma>'"
  shows "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr' @ tr\<rangle> \<sigma>''" 
  using assms 
proof (induction arbitrary:  tr' \<sigma> rule: internal_exec_rev'.induct )
  case (internal_refl \<sigma>)
  thus ?case by simp
next
  case (internal_step \<sigma> \<sigma>' c c' tr \<sigma>'')
  thus ?case
  proof -
    have "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>(tr' @ [\<sigma>']) @ tr\<rangle> \<sigma>''"
      by (meson internal_exec.simps internal_step internal_step)
    thus ?thesis 
      by simp
  qed
qed

lemma internal_exec_appI1:
  assumes  "internal_exec M M' \<sigma> tr \<sigma>' " 
           "internal_exec_rev' M M' \<sigma>' tr' \<sigma>'' "
  shows    "internal_exec_rev M M' \<sigma> (tr @ tr') \<sigma>''"

  using assms internal_exec_rev_appI trace_rev1 
  by blast

lemma trace_rev2: 
  "internal_exec_rev M M' \<sigma> tr \<sigma>' \<Longrightarrow> internal_exec M M' \<sigma> tr \<sigma>' "
proof  (induction rule: internal_exec_rev.induct)
  case (internal_exec_rev_first_step \<sigma> \<sigma>' c c' tr \<sigma>'')
  note facts = internal_exec_rev_first_step 
  from facts(7) 
  show ?case
  proof(cases rule: internal_exec_rev'.cases)
    case internal_refl
    thus ?thesis  
      using internal_exec_first_step facts 
      by blast
  next    
    case (internal_step \<sigma>''' c c' tr')
    thus ?thesis 
      using internal_exec_appI internal_exec_first_step 
            internal_exec_rev_first_step 
      by (metis (full_types) append_Cons  self_append_conv2)
    qed
qed

lemma trace_rev: 
  "internal_exec_rev M M' \<sigma> tr \<sigma>' = internal_exec M M' \<sigma> tr \<sigma>' "
  using trace_rev1 trace_rev2 
  by blast
(* Given two internal executions from the same starting state, one has to be a prefix
        of the other. *)
lemma internal_exec_rev'_det_prefix:
  "internal_exec_rev' M M' \<sigma> tr \<sigma>'   \<Longrightarrow> 
   internal_exec_rev' M M' \<sigma> tr' \<sigma>'' \<Longrightarrow>
   (\<exists>tr''. (tr = tr' @ tr'') \<or> (tr' = tr @ tr''))"
proof(induction arbitrary: tr' \<sigma>'' rule: internal_exec_rev'.induct)
  case (internal_refl \<sigma>)
  thus ?case by blast
next
  case (internal_step \<sigma> \<sigma>' c c' tr \<sigma>'')
  note facts = internal_step
  from internal_step(8) 
  show ?case
  proof(cases rule: internal_exec_rev'.cases)
    case internal_refl
    thus ?thesis 
      by blast
  next
    case (internal_step \<sigma> c c' tr)
    thus ?thesis
      using exec_det_aux facts 
      by (metis append_Cons)
  qed
qed

lemma internal_exec_rev_det_prefix':
  "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>ir\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> 
  M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>ir\<langle>tr'\<rangle> v \<Longrightarrow>  
  (\<exists> tr''.(tr = (tr' @ tr'')) \<or> (tr' = tr @ tr''))"
proof(induction arbitrary: tr' v rule: internal_exec_rev.induct)
  case (internal_exec_rev_first_step  \<sigma> \<sigma>' c c' tr \<sigma>'')
  note facts = internal_exec_rev_first_step
  from \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>ir\<langle>tr'\<rangle> v\<close> 
  show ?case
  proof (cases rule: internal_exec_rev.cases)
    case (internal_exec_rev_first_step \<sigma>''' c'' c''' tr'')
    have "\<sigma>''' = \<sigma>'" 
      using facts(2) internal_exec_rev_first_step(3) exec_det_aux 
      by blast
    with facts internal_exec_rev_first_step 
    show ?thesis 
      using internal_exec_rev'_det_prefix  
      by auto
  qed
qed

lemma internal_exec_det_prefix':
  "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> 
  M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> v \<Longrightarrow>  
  (\<exists> tr''.(tr = tr' @ tr'') \<or> (tr' = tr @ tr''))"
  using internal_exec_rev_det_prefix' trace_rev 
  by blast

inductive_cases internal_exec_elim [elim!]: "internal_exec M M' \<sigma> tr \<sigma>''"
inductive_cases visible_exec_elim [elim!]: "visible_exec M M' \<sigma> \<sigma>''"

lemma internal_exec_det_aux:
 "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> v \<Longrightarrow>  v = \<sigma>'"
  by (metis internal_exec_elim last_ConsL last_snoc)

lemma internal_exec_is_internal:
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow>
   \<forall>\<sigma>\<^sub>i \<in> set tr.(\<exists> c.(this_class_lookup \<sigma>\<^sub>i = Some c \<and> c \<in> dom M))"
  by (induction rule: internal_exec.induct) simp+

lemma internal_exec_appD:
 assumes "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> \<sigma>'"
 shows  "\<forall>tr'' \<sigma>\<^sub>i. (M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr' @ tr''\<rangle> \<sigma>\<^sub>i) \<longrightarrow> 
        (internal_exec_rev' M M' \<sigma>' tr'' \<sigma>\<^sub>i)"
  using assms 
proof (induction tr' arbitrary: \<sigma> \<sigma>' rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  note facts = internal_exec_more_steps
  fix tr'' \<sigma>\<^sub>i 
  have x_eq [simp]: "x = \<sigma>'" 
    using snoc.prems 
    by auto
  hence "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>xs @ [\<sigma>']\<rangle> \<sigma>'" 
    using snoc.prems 
    by blast
  from \<open> M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>xs @ [x]\<rangle> \<sigma>'\<close>  
  show ?case
  proof (cases rule: internal_exec.cases)
    case (internal_exec_first_step c c')
    hence xs_Nil [simp]: "xs = []" 
      by simp
    show ?thesis 
    proof(intro allI impI)
      fix tr'' \<sigma>\<^sub>i
      assume "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>(xs @ [x]) @ tr''\<rangle> \<sigma>\<^sub>i"
      hence "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>x # tr''\<rangle> \<sigma>\<^sub>i"
        by simp
      hence "internal_exec_rev M M' \<sigma> (x#tr'') \<sigma>\<^sub>i" 
        using trace_rev 
        by simp
      thus "M;M',\<sigma>' \<rightarrow>\<^bsub>e\<^esub>ir1\<langle>tr''\<rangle> \<sigma>\<^sub>i"
        apply (rule internal_exec_rev.cases)
        by simp
    qed
  next
    case (internal_exec_more_steps tr \<sigma>'' c)   
    note facts = internal_exec_more_steps   
    hence xs_tr [simp]: "xs = tr"  
      by blast  
    have internal_xs: "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr @ [\<sigma>']\<rangle> \<sigma>'" 
      using snoc.prems 
      by auto
    from this 
    obtain \<sigma>tr 
      where "(M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>tr) \<and> 
             (internal_exec_rev' M M' \<sigma>tr [\<sigma>'] \<sigma>')"
      using snoc(1) xs_tr internal_exec_more_steps 
      by metis     
    with snoc(1) have
      IH: "\<forall>tr'' \<sigma>\<^sub>i. (M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>xs @ tr''\<rangle> \<sigma>\<^sub>i) 
            \<longrightarrow> (M;M',\<sigma>tr \<rightarrow>\<^bsub>e\<^esub>ir1\<langle>tr''\<rangle> \<sigma>\<^sub>i)"
      by (metis xs_tr)
    show ?thesis
    proof(intro allI impI)
      fix tr'' \<sigma>\<^sub>i
      assume "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>(xs @ [x]) @ tr''\<rangle> \<sigma>\<^sub>i"
      hence "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>xs @ (x # tr'')\<rangle> \<sigma>\<^sub>i" 
        by simp
      with IH have "M;M',\<sigma>tr \<rightarrow>\<^bsub>e\<^esub>ir1\<langle>x # tr''\<rangle> \<sigma>\<^sub>i" 
        by metis
      thus " M;M',\<sigma>' \<rightarrow>\<^bsub>e\<^esub>ir1\<langle>tr''\<rangle> \<sigma>\<^sub>i"  
        apply (cases rule: internal_exec_rev'.cases)        
        using x_eq 
        by blast      
    qed
  qed
qed

lemma internal_exec_appD1:
  assumes "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> \<sigma>'"
          "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr' @ tr''\<rangle> \<sigma>\<^sub>i"
  shows   "internal_exec_rev' M M' \<sigma>' tr'' \<sigma>\<^sub>i"

  using assms internal_exec_appD 
  by metis 

lemma visible_exec_det_aux:
  "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> link_wf M M' \<Longrightarrow> 
   M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow> \<sigma>'' = \<sigma>'"
proof(induction arbitrary: \<sigma>'' rule: visible_exec.induct)
  case (visible_exec_intro M M' \<sigma> tr \<sigma>\<^sub>i \<sigma>' c)
  note facts = visible_exec_intro
  from \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close> 
  show ?case 
  proof(cases rule: visible_exec.cases)
    case (visible_exec_intro tr' \<sigma>\<^sub>i' c)
    note facts1 = visible_exec_intro
    from \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>\<^sub>i\<close> have
      "\<forall>\<sigma>\<^sub>i \<in> set tr. 
       (\<exists> c. this_class_lookup \<sigma>\<^sub>i = Some c \<and> c \<in> dom M)"
      using internal_exec_is_internal 
      by auto
    from \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> \<sigma>\<^sub>i'\<close> have
      "\<forall>\<sigma>\<^sub>i \<in> set tr'. 
       (\<exists> c. this_class_lookup \<sigma>\<^sub>i = Some c \<and> c \<in> dom M)"
      using internal_exec_is_internal 
      by auto
    obtain tr'' where tr: "tr = tr' @ tr'' \<or> tr' = tr @ tr''"
      using facts(1) visible_exec_intro(1) internal_exec_det_prefix'
      by metis
    hence "tr'' = []"  
    proof (rule disjE)
      show " tr = tr' @ tr'' \<Longrightarrow> tr'' = []"
      proof (rule ccontr)
        assume tr_def: "tr = tr' @ tr''" "\<not>(tr'' = [])"
        from \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>\<^sub>i\<close> 
        have "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr' @ tr''\<rangle> \<sigma>\<^sub>i" 
          using tr_def 
          by simp
      from this and \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> \<sigma>\<^sub>i'\<close> 
      have inter_ex:  "internal_exec_rev' M M' \<sigma>\<^sub>i' tr'' \<sigma>\<^sub>i" 
        using internal_exec_appD1 
        by auto
      hence  "tr'' = []"
        proof (cases rule: internal_exec_rev'.cases)
          case internal_refl
          thus ?thesis 
            by simp
        next
          case (internal_step \<sigma>' c' c'' tr)
          from facts1(2) internal_step(2) 
          have a1: "\<sigma>'' = \<sigma>'" 
            using exec_det_aux 
            by auto
        from facts1 internal_step 
        have a2: "this_class_lookup \<sigma>'' = Some c \<and> c \<in> dom M'" and 
             a3: "this_class_lookup \<sigma>' = Some c'' \<and> c'' \<in> dom M" 
           apply blast 
          using local.internal_step(5) local.internal_step(6) 
          by auto
        have a4: "c \<in> dom M' \<and> c'' \<in> dom M" 
          by (simp add: local.internal_step(6) 
              local.visible_exec_intro(4))
        from a1 a2 a3 
        have a5: " c =  c''" 
            by simp
          from a4 a5 show ?thesis 
            using link_wf_def visible_exec_intro.prems(1) 
            by auto 
        qed
        thus False 
          using \<open>tr'' \<noteq> []\<close> 
          by auto
      qed 
      show "tr' = tr @ tr'' \<Longrightarrow> tr'' = []"
      proof (rule ccontr)
        assume tr_def1: "tr' = tr @ tr''" "\<not>(tr'' = [])"
        from \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr'\<rangle> \<sigma>\<^sub>i'\<close>
        have "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr @ tr''\<rangle> \<sigma>\<^sub>i'" 
          using tr_def1 by simp
        from this and \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>\<^sub>i\<close> 
        have inter_ex1: "internal_exec_rev' M M' \<sigma>\<^sub>i tr'' \<sigma>\<^sub>i'" 
          using internal_exec_appD1 
          by auto
        hence  "tr'' = []"
        proof (cases rule: internal_exec_rev'.cases)
          case internal_refl
          thus ?thesis 
            by simp
        next
          case (internal_step \<sigma>' c' c'' tr)
          thus ?thesis using facts exec_det_aux link_wf_def 
            by (metis IntI empty_iff option.inject)            
        qed
        thus False 
          using \<open>tr'' \<noteq> []\<close> by auto
      qed
    qed
    thus ?thesis  
      using facts1 tr exec_det_aux append.right_neutral 
        internal_exec_det_aux visible_exec_intro.hyps(1) 
        visible_exec_intro.hyps(2)
      by metis
  qed
qed
end