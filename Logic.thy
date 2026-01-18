theory Logic
imports Adaptation
begin

(*Authour: Duc Than Nguyen *) 

text \<open>Module pairs and visible states semantics\<close>

text \<open>
  A visible execution is a sequence of execution steps that look like this:
  @{text "\<sigma> \<leadsto> \<sigma>\<^sub>2 \<leadsto> ... \<sigma>\<^bsub>n-1\<^esub> \<leadsto> \<sigma>\<^sub>n"} where, the class of the "this" object in
  @{term \<sigma>} comes from the external module @{term M'}, and the class of the
  "this" object in @{term "\<sigma>\<^sub>n"} also comes from the external module @{term M'}. But
  the class of the "this" object in every other @{term "\<sigma>\<^sub>2"}, ... @{text "\<sigma>\<^bsub>(n-1)\<^esub>"} 
  comes from the internal
  module @{term M}.

  We capture this using two inductive definitions.
  The first one talks about the first  @{term "n-2"} steps of execution, 
  each such step leads to a configuration @{term "\<sigma>\<^sub>i"}
  where @{text "2 \<le> i < n"} in which the "this" object of @{term \<sigma>\<^sub>i} is in the internal
  module @{term M}.

  The second inductive definition is just for the final step from @{text "\<sigma> \<^bsub>n-1\<^esub>"} to @{term \<sigma>\<^sub>n }.
\<close>

inductive internal_exec :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> (Config list) \<Rightarrow> Config \<Rightarrow> bool" ("_;_,_ \<leadsto>i\<langle>_\<rangle> _") for
  M :: Module and M' :: Module where
  internal_exec_first_step:
  "link_wf M M' \<Longrightarrow> 
   (M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow>
   this_class_lookup \<sigma> = Some c \<Longrightarrow> c \<in> dom M' \<Longrightarrow>
   this_class_lookup \<sigma>' = Some c' \<Longrightarrow> c' \<in> dom M \<Longrightarrow>
   internal_exec M M' \<sigma> [\<sigma>'] \<sigma>'" |
  internal_exec_more_steps:
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow>
   (M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow>
   this_class_lookup \<sigma>'' = Some c \<Longrightarrow> c \<in> dom M  \<Longrightarrow>
   internal_exec M M' \<sigma> (tr@[\<sigma>'']) \<sigma>''"


inductive internal_exec_rev' :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> (Config list) \<Rightarrow> Config \<Rightarrow> bool" ("_;_,_ \<leadsto>ir1\<langle>_\<rangle> _") 
  for M :: Module and M' :: Module where
  internal_refl: "internal_exec_rev' M M' \<sigma> [] \<sigma>" |
  internal_step: "(M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> this_class_lookup \<sigma> = Some c \<Longrightarrow> c \<in> dom M \<Longrightarrow>
    this_class_lookup \<sigma>' = Some c' \<Longrightarrow> c' \<in> dom M \<Longrightarrow> 
    internal_exec_rev' M M' \<sigma>' tr \<sigma>'' \<Longrightarrow>
    internal_exec_rev' M M' \<sigma> (\<sigma>'#tr) \<sigma>''"

inductive internal_exec_rev :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> (Config list) \<Rightarrow> Config \<Rightarrow> bool" ("_;_,_ \<leadsto>ir\<langle>_\<rangle> _") 
  for M :: Module and M' :: Module where
  internal_exec_rev_first_step:
  "link_wf M M' \<Longrightarrow>
   (M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow>
   this_class_lookup \<sigma> = Some c \<Longrightarrow> c \<in> dom M' \<Longrightarrow>
   this_class_lookup \<sigma>' = Some c' \<Longrightarrow> c' \<in> dom M \<Longrightarrow>
   internal_exec_rev' M M' \<sigma>' tr \<sigma>'' \<Longrightarrow>
   internal_exec_rev M M' \<sigma> (\<sigma>'#tr) \<sigma>''" 

thm internal_exec_rev.induct
thm internal_exec_rev'.induct

lemma internal_exec_rev_tr_nonempty':
  "internal_exec_rev M M' \<sigma> tr \<sigma>' \<Longrightarrow> tr = [] \<Longrightarrow> False"
  apply(induction rule: internal_exec_rev.induct, auto)
  done

lemma internal_exec_rev_tr_nonempty:
  "internal_exec_rev M M' \<sigma> [] \<sigma>' \<Longrightarrow> False"
  using internal_exec_rev_tr_nonempty' by blast


lemma internal_exec_rev'_appI:
  "internal_exec_rev' M M' \<sigma> tr \<sigma>' \<Longrightarrow>
   internal_exec_rev' M M' \<sigma>' tr' \<sigma>'' \<Longrightarrow>
   internal_exec_rev' M M' \<sigma> (tr @ tr') \<sigma>''"
  apply(induct rule: internal_exec_rev'.induct)
   apply simp
  by (simp add: internal_step)

lemma internal_exec_rev_appI:
  assumes "internal_exec_rev M M' \<sigma> tr \<sigma>'''"
  assumes "internal_exec_rev' M M' \<sigma>''' tr' \<sigma>''"
  shows "internal_exec_rev M M' \<sigma> (tr @ tr') \<sigma>''"
  using assms apply(induction tr arbitrary: \<sigma> \<sigma>''' tr' \<sigma>'')
  using internal_exec_rev_tr_nonempty apply blast
  apply(erule internal_exec_rev.cases)
  by (simp add: internal_exec_rev'_appI internal_exec_rev_first_step)  

lemma trace_rev1: 
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow> internal_exec_rev M M' \<sigma> tr \<sigma>'"
proof  (induction rule: internal_exec.induct)
   case (internal_exec_first_step \<sigma> \<sigma>' c c')    
   then show ?case 
   by (simp add: internal_exec_rev_first_step internal_refl)
next 
   case (internal_exec_more_steps \<sigma> tr \<sigma>' \<sigma>'' c)  
   note facts = internal_exec_more_steps
   then show ?case
   proof (cases rule: internal_exec.cases)
     case (internal_exec_first_step c c')
     then show ?thesis 
       using facts internal_exec_rev_first_step internal_refl internal_step 
       by auto
   next
     case (internal_exec_more_steps tr' \<sigma>''' c')
     then show ?thesis using internal_exec_rev_appI  facts internal_refl internal_step 
       by blast
   qed
 qed


lemma internal_exec_tr_nonempty:
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow> tr = [] \<Longrightarrow> False"
  by(induct rule: internal_exec.induct, auto)

lemma internal_exec_tr_nonempty' [simp]:
  "internal_exec M M' \<sigma> [] \<sigma>' = False"
  using internal_exec_tr_nonempty by blast

(*internal_exec_rev' (the second premise) *)

lemma internal_exec_appI:  
  assumes "internal_exec_rev' M M' \<sigma>' tr \<sigma>''"
          "M;M', \<sigma> \<leadsto>i\<langle>tr'\<rangle> \<sigma>'"
  shows "M;M',\<sigma> \<leadsto>i\<langle>tr' @ tr\<rangle> \<sigma>''"  
using assms proof (induction arbitrary:  tr' \<sigma> rule: internal_exec_rev'.induct )
  case (internal_refl \<sigma>)
  then show ?case 
    by simp

next
  case (internal_step \<sigma> \<sigma>' c c' tr \<sigma>'')
  then show ?case
  proof -
    have "M;M',\<sigma> \<leadsto>i\<langle>(tr' @ [\<sigma>']) @ tr\<rangle> \<sigma>''"
      by (meson internal_exec.simps internal_step internal_step)
  then show ?thesis by simp
  qed
qed

lemma internal_exec_appI1:
  assumes  "internal_exec M M' \<sigma> tr \<sigma>' " 
           "internal_exec_rev' M M' \<sigma>' tr' \<sigma>'' "
  shows    "internal_exec_rev M M' \<sigma> (tr @ tr') \<sigma>''"
  using assms internal_exec_rev_appI trace_rev1 by blast


lemma trace_rev2: 
  "internal_exec_rev M M' \<sigma> tr \<sigma>' \<Longrightarrow> internal_exec M M' \<sigma> tr \<sigma>' "
proof  (induction rule: internal_exec_rev.induct)
  case (internal_exec_rev_first_step \<sigma> \<sigma>' c c' tr \<sigma>'')
  note facts = internal_exec_rev_first_step 
  from facts(7)  show ?case
  proof(cases rule: internal_exec_rev'.cases)
    case internal_refl
    then show ?thesis 
      using internal_exec_first_step facts by blast
  next    
    case (internal_step \<sigma>''' c c' tr')
    then show ?thesis using internal_exec_appI 
      by (metis (full_types) append_Cons internal_exec_first_step internal_exec_rev_first_step self_append_conv2)
    qed
qed

lemma trace_rev: 
  "internal_exec_rev M M' \<sigma> tr \<sigma>' = internal_exec M M' \<sigma> tr \<sigma>' "
  using trace_rev1 trace_rev2 by blast


text \<open> Given two internal executions from the same starting state, one has to be a prefix
        of the other. \<close>


lemma internal_exec_rev'_det_prefix:
  "internal_exec_rev' M M' \<sigma> tr \<sigma>'   \<Longrightarrow> internal_exec_rev' M M' \<sigma> tr' \<sigma>'' \<Longrightarrow>
   (\<exists>tr''. (tr = tr' @ tr'') \<or> (tr' = tr @ tr''))"
proof(induction arbitrary: tr' \<sigma>'' rule: internal_exec_rev'.induct)
  case (internal_refl \<sigma>)
  then show ?case by blast
next
  case (internal_step \<sigma> \<sigma>' c c' tr \<sigma>'')
  note facts = internal_step
  from internal_step(8) show ?case
  proof(cases rule: internal_exec_rev'.cases)
    case internal_refl
    then show ?thesis by blast
  next
    case (internal_step \<sigma> c c' tr)
    then show ?thesis
      using exec_det facts 
      by (metis append_Cons)
  qed
qed

lemma internal_exec_rev_det_prefix':
 "M;M', \<sigma> \<leadsto>ir\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> M;M', \<sigma> \<leadsto>ir\<langle>tr'\<rangle> v \<Longrightarrow>  
  (\<exists> tr''. (tr = (tr' @ tr'')) \<or>  (tr' = tr @ tr''))"
proof(induction arbitrary: tr' v rule: internal_exec_rev.induct)
  case (internal_exec_rev_first_step  \<sigma> \<sigma>' c c' tr \<sigma>'')
  note facts = internal_exec_rev_first_step
  thm facts(2)
  from `M;M',\<sigma> \<leadsto>ir\<langle>tr'\<rangle> v` show ?case
  proof(cases rule: internal_exec_rev.cases)
    case (internal_exec_rev_first_step \<sigma>''' c'' c''' tr'')
    have "\<sigma>''' = \<sigma>'" using facts(2) internal_exec_rev_first_step(3) using exec_det by blast
    with facts internal_exec_rev_first_step show ?thesis using internal_exec_rev'_det_prefix  by auto
  qed
qed


lemma internal_exec_det_prefix':
 "M;M', \<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> M;M', \<sigma> \<leadsto>i\<langle>tr'\<rangle> v \<Longrightarrow>  
  (\<exists> tr''. (tr = tr' @ tr'') \<or>  (tr' = tr @ tr''))"
  using internal_exec_rev_det_prefix' trace_rev by blast

inductive visible_exec :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> Config \<Rightarrow> bool" ("_;_,_ \<leadsto> _") where
  visible_exec_intro: "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow>
   (M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow>
   this_class_lookup \<sigma>'' = Some c \<Longrightarrow> c \<in> dom M'  \<Longrightarrow>
   visible_exec M M' \<sigma> \<sigma>''"


inductive_cases internal_exec_elim [elim!]: " internal_exec M M' \<sigma> tr \<sigma>''"
inductive_cases visible_exec_elim [elim!]: " visible_exec M M' \<sigma> \<sigma>''"

thm internal_exec_elim

lemma internal_exec_det:
 "M;M', \<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> M;M', \<sigma> \<leadsto>i\<langle>tr\<rangle> v \<Longrightarrow>  v = \<sigma>'"
  by (metis internal_exec_elim last_ConsL last_snoc)

lemma internal_exec_is_internal:
  "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow>
   \<forall>\<sigma>\<^sub>i \<in> set tr. (\<exists> c. this_class_lookup \<sigma>\<^sub>i = Some c \<and> c \<in> dom M)"
  by (induction rule: internal_exec.induct) simp+

lemma internal_exec_appD:
 assumes "M;M',\<sigma> \<leadsto>i\<langle>tr'\<rangle> \<sigma>'"
 shows  "\<forall>tr'' \<sigma>\<^sub>i. (M;M',\<sigma> \<leadsto>i\<langle>tr' @ tr''\<rangle> \<sigma>\<^sub>i) \<longrightarrow> (internal_exec_rev' M M' \<sigma>' tr'' \<sigma>\<^sub>i)"
  using assms proof (induction tr' arbitrary: \<sigma> \<sigma>'  rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  note facts = internal_exec_more_steps
  fix tr'' \<sigma>\<^sub>i 
  have x_eq[simp]: "x = \<sigma>'" 
    using snoc.prems by auto
  from this 
  have  "M;M',\<sigma> \<leadsto>i\<langle>xs @ [\<sigma>']\<rangle> \<sigma>'" 
    using snoc.prems by blast
  from ` M;M',\<sigma> \<leadsto>i\<langle>xs @ [x]\<rangle> \<sigma>'`  
  show ?case
  proof (cases rule: internal_exec.cases)
    case (internal_exec_first_step c c')
    then have xs_Nil[simp]: "xs = []" 
      by simp
    show ?thesis 
    proof(intro allI impI)
      fix tr'' \<sigma>\<^sub>i
      assume "M;M',\<sigma> \<leadsto>i\<langle>(xs @ [x]) @ tr''\<rangle> \<sigma>\<^sub>i"
      hence "M;M',\<sigma> \<leadsto>i\<langle>x # tr''\<rangle> \<sigma>\<^sub>i"
        by simp
      hence "internal_exec_rev M M' \<sigma> (x#tr'') \<sigma>\<^sub>i" using trace_rev by simp
      thus "M;M',\<sigma>' \<leadsto>ir1\<langle>tr''\<rangle> \<sigma>\<^sub>i"
        apply (rule internal_exec_rev.cases)
        apply simp
        done
    qed
  next
    case (internal_exec_more_steps tr \<sigma>'' c)   
    note facts = internal_exec_more_steps   

    from this have xs_tr[simp]: "xs = tr" 
      by blast  
    have internal_xs: "M;M',\<sigma> \<leadsto>i\<langle>tr @ [\<sigma>']\<rangle> \<sigma>'" 
      using snoc.prems by auto
    from this obtain \<sigma>tr where "(M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>tr) \<and> (internal_exec_rev' M M' \<sigma>tr [\<sigma>'] \<sigma>')"
      using snoc(1) xs_tr internal_exec_more_steps by metis     
    with snoc(1) have
      IH: "\<forall>tr'' \<sigma>\<^sub>i. (M;M',\<sigma> \<leadsto>i\<langle>xs @ tr''\<rangle> \<sigma>\<^sub>i) \<longrightarrow> (M;M',\<sigma>tr \<leadsto>ir1\<langle>tr''\<rangle> \<sigma>\<^sub>i)"
      by (metis xs_tr)

    show ?thesis 
    proof(intro allI impI)
      fix tr'' \<sigma>\<^sub>i
      assume "M;M',\<sigma> \<leadsto>i\<langle>(xs @ [x]) @ tr''\<rangle> \<sigma>\<^sub>i"
      hence "M;M',\<sigma> \<leadsto>i\<langle>xs @ (x # tr'')\<rangle> \<sigma>\<^sub>i" by simp
      with IH have "M;M',\<sigma>tr \<leadsto>ir1\<langle>x # tr''\<rangle> \<sigma>\<^sub>i" by metis
      then show " M;M',\<sigma>' \<leadsto>ir1\<langle>tr''\<rangle> \<sigma>\<^sub>i"  
        apply (cases rule: internal_exec_rev'.cases)        
        using x_eq by blast      
    qed
  qed
qed

lemma internal_exec_appD1:
  assumes "M;M',\<sigma> \<leadsto>i\<langle>tr'\<rangle> \<sigma>'"
          "M;M',\<sigma> \<leadsto>i\<langle>tr' @ tr''\<rangle> \<sigma>\<^sub>i"
  shows   "internal_exec_rev' M M' \<sigma>' tr'' \<sigma>\<^sub>i"
  using assms internal_exec_appD by metis 


(*We need to prove deterministic for internal_exec first *) 
lemma visible_exec_det:
  "M;M', \<sigma> \<leadsto> \<sigma>' \<Longrightarrow> link_wf M M' \<Longrightarrow> M;M', \<sigma> \<leadsto> \<sigma>'' \<Longrightarrow> \<sigma>'' = \<sigma>'"
proof(induction arbitrary: \<sigma>'' rule: visible_exec.induct)
  case (visible_exec_intro M M' \<sigma> tr \<sigma>\<^sub>i \<sigma>' c)
  note facts = visible_exec_intro
  from `M;M',\<sigma> \<leadsto> \<sigma>''` 
  show ?case 
  proof(cases rule: visible_exec.cases)
    case (visible_exec_intro tr' \<sigma>\<^sub>i' c)
    note facts1 = visible_exec_intro
    from `M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>\<^sub>i` have
      "\<forall>\<sigma>\<^sub>i \<in> set tr. (\<exists> c. this_class_lookup \<sigma>\<^sub>i = Some c \<and> c \<in> dom M)"
      using internal_exec_is_internal by auto
    from `M;M',\<sigma> \<leadsto>i\<langle>tr'\<rangle> \<sigma>\<^sub>i'` have
      "\<forall>\<sigma>\<^sub>i \<in> set tr'. (\<exists> c. this_class_lookup \<sigma>\<^sub>i = Some c \<and> c \<in> dom M)"
      using internal_exec_is_internal by auto
    obtain tr'' where tr:"tr = tr' @ tr'' \<or> tr' = tr @ tr''"
      using facts(1) visible_exec_intro(1) internal_exec_det_prefix'
      by metis

    from this 
    have "tr'' = []" 
    proof (rule disjE)
      show " tr = tr' @ tr'' \<Longrightarrow> tr'' = []"
      proof (rule ccontr)
        assume tr_def: "tr = tr' @ tr''" "\<not>(tr'' = [])"
        from `M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>\<^sub>i` 
      have "M;M',\<sigma> \<leadsto>i\<langle>tr' @ tr''\<rangle> \<sigma>\<^sub>i" using tr_def by simp
      from this and `M;M',\<sigma> \<leadsto>i\<langle>tr'\<rangle> \<sigma>\<^sub>i'` 
      have inter_ex:  "internal_exec_rev' M M' \<sigma>\<^sub>i' tr'' \<sigma>\<^sub>i" 
        using internal_exec_appD1 by auto 

        from this have  "tr'' = []"
        proof (cases rule: internal_exec_rev'.cases)
          case internal_refl
          then show ?thesis 
            by simp
        next
          case (internal_step \<sigma>' c' c'' tr)
        from facts1(2) internal_step(2) have a1: "\<sigma>'' = \<sigma>'" 
          using exec_det by auto
        from facts1 internal_step 
        have a2: "this_class_lookup \<sigma>'' = Some c \<and> c \<in> dom M'" and 
             a3: "this_class_lookup \<sigma>' = Some c'' \<and> c'' \<in> dom M" 
           apply blast 
          using local.internal_step(5) local.internal_step(6) by auto
        have a4: "c \<in> dom M' \<and> c'' \<in> dom M" 
          by (simp add: local.internal_step(6) local.visible_exec_intro(4))
          from a1  a2 a3 have a5: " c =  c''" 
            by simp
          from a4 a5 show ?thesis 
            using link_wf_def visible_exec_intro.prems(1) by auto 
        qed

        from this show False 
          using \<open>tr'' \<noteq> []\<close> by auto
      qed 

      show "tr' = tr @ tr'' \<Longrightarrow> tr'' = []"
      proof (rule ccontr)
        assume tr_def1: "tr' = tr @ tr''" "\<not>(tr'' = [])"
        from `M;M',\<sigma> \<leadsto>i\<langle>tr'\<rangle> \<sigma>\<^sub>i'`
        have "M;M',\<sigma> \<leadsto>i\<langle>tr @ tr''\<rangle> \<sigma>\<^sub>i'" using tr_def1 by simp
        from this and `M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>\<^sub>i` 
        have inter_ex1:  "internal_exec_rev' M M' \<sigma>\<^sub>i tr'' \<sigma>\<^sub>i'" 
          using internal_exec_appD1 by auto

        from this have  "tr'' = []"
        proof (cases rule: internal_exec_rev'.cases)
          case internal_refl
          then show ?thesis 
            by simp
        next
          case (internal_step \<sigma>' c' c'' tr)
          then show ?thesis using facts exec_det link_wf_def 
            by (metis IntI empty_iff option.inject)            
        qed

        thus False 
          using \<open>tr'' \<noteq> []\<close> by auto
      qed
    qed
    from this show ?thesis 
      using facts1 tr exec_det  
      by (metis append.right_neutral internal_exec_det visible_exec_intro.hyps(1) visible_exec_intro.hyps(2))
  qed
qed



(*define link_wf_3M for 3 modules whose domains are pairwise disjoint*)
definition 
  link_wf_3M :: "Module \<Rightarrow> Module \<Rightarrow> Module \<Rightarrow> bool"
  where
  "link_wf_3M M M' M'' \<equiv> ((dom M \<inter> dom M' = {}) \<and> (dom M' \<inter> dom M'' = {})
                      \<and>  (dom M'' \<inter> dom M = {}))"

lemma link_dom [simp]:
  "dom (M \<circ>\<^bsub>l\<^esub> M') = dom M \<union> dom M'"
  apply(auto simp: moduleLinking_def moduleAux_def dom_def)
  done

lemma link_wf_3M_dest [simp,intro,dest]: 
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf M M'"
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf M' M''"
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf M M''"
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf (M \<circ>\<^bsub>l\<^esub> M') M'' "
  by(fastforce simp: link_wf_def link_wf_3M_def)+


lemma internal_linking1: "\<lbrakk>M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'; link_wf_3M M M' M''\<rbrakk> \<Longrightarrow> M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'"
proof (induction rule: internal_exec.induct)
  case (internal_exec_first_step  \<sigma> \<sigma>' c c')
  have a:  "link_wf M (M' \<circ>\<^bsub>l\<^esub> M'')"
    using `link_wf_3M M M' M''`
    by(fastforce simp: link_wf_def link_wf_3M_def)
  have wf: "link_wf M M'" using `link_wf_3M M M' M''` by simp
 
  have  "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
    apply(rule link_exec)
     apply(rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'\<close>)
    using \<open>(link_wf_3M M M' M'')\<close> link_wf_3M_dest by blast
    
  from this wf link_assoc have b: "(M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'')), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
    by metis    

  have "dom (M' \<circ>\<^bsub>l\<^esub> M'') = dom M' \<union> dom M''" 
    by (simp add: \<open>link_wf_3M M M' M''\<close>)

  hence c: "this_class_lookup \<sigma> = Some c \<and> c \<in> dom (M' \<circ>\<^bsub>l\<^esub> M'')" 
    using internal_exec_first_step
    by blast

  from a b c internal_exec_first_step
  show ?case 
    using internal_exec.internal_exec_first_step by blast
next
  case (internal_exec_more_steps  \<sigma> tr \<sigma>' \<sigma>'' c)

  have a: "M;M' \<circ>\<^bsub>l\<^esub> M'',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>' "
    using \<open>link_wf_3M M M' M'' \<Longrightarrow> M;M' \<circ>\<^bsub>l\<^esub> M'',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'\<close> and \<open>link_wf_3M M M' M''\<close> by simp

  have asm: "M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'') = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''" 
    by (metis internal_exec_more_steps.prems link_assoc link_wf_3M_dest(1))

  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' "
    apply (rule link_exec)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_dest by blast

  from this and asm
  have b: "(M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'')), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" by simp

  have c: "this_class_lookup \<sigma>'' = Some c \<and> (c \<in> dom M)" 
      using internal_exec_more_steps by auto

    from a b c internal_exec.internal_exec_more_steps 
  show ?case by simp
qed

(*using internal_linking1 to prove the lemma *)
(* M;M',\<sigma> \<leadsto> \<sigma>'  implies M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<leadsto> \<sigma>'  *)

lemma visible_exec_linking1:
  "\<lbrakk>(M;M',\<sigma> \<leadsto> \<sigma>'); (link_wf_3M M M' M'')\<rbrakk> \<Longrightarrow> M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<leadsto> \<sigma>'"
proof (induction rule: visible_exec.induct)
  case (visible_exec_intro M M' \<sigma> tr \<sigma>' \<sigma>'' c)

  have a: "M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'"  
    using \<open> M; M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'\<close> by (simp add: visible_exec_intro internal_linking1)

  have asm: "M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'') = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''" 
    by (metis link_assoc link_wf_3M_dest(1) visible_exec_intro.prems)

  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' "
    apply (rule link_exec)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_dest by blast

  from this and asm
  have b: "(M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'')), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" by simp
  have c: "this_class_lookup \<sigma>'' = Some c \<and> ( c\<in> dom (M' \<circ>\<^bsub>l\<^esub> M''))"
    using \<open>this_class_lookup \<sigma>'' = Some c\<close> and \<open>c \<in> dom M'\<close> by simp
  from a b c show ?case 
    using visible_exec.visible_exec_intro by simp
qed


lemma internal_linking2: " M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> link_wf_3M M M' M''\<Longrightarrow> (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'"
proof (induction rule: internal_exec.induct)
  case (internal_exec_first_step \<sigma> \<sigma>' c c')
  have a: "link_wf (M \<circ>\<^bsub>l\<^esub> M'') M'" using `link_wf_3M M M' M''` 
    by (fastforce simp add: link_wf_def link_wf_3M_def)

   have " M\<circ>\<^bsub>l\<^esub> M'' = M''\<circ>\<^bsub>l\<^esub> M "  using \<open>link_wf_3M M M' M''\<close> link_commute by blast
  from this have "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' =  M''\<circ>\<^bsub>l\<^esub> (M \<circ>\<^bsub>l\<^esub> M')" 
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_def link_wf_def 
    by (metis internal_exec_first_step.hyps(1) internal_exec_first_step.prems 
        link_assoc link_commute link_wf_3M_dest(2) link_wf_3M_dest(3) link_wf_3M_dest(4)) 
  from this have "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub>M''"
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  from this have asm:  "(M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = (M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'" by simp

  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'" 
    apply (rule link_exec)
     apply (rule `(M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'`)
    using internal_exec_first_step by blast
  from this and asm  
have b: " ((M \<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'" by simp
 
  have c: " this_class_lookup \<sigma> = Some c  \<and>  (c \<in> dom M') "
    using internal_exec_first_step by auto

  have d: "this_class_lookup \<sigma>' = Some c' \<and> (c' \<in> dom (M \<circ>\<^bsub>l\<^esub> M''))" 
    using internal_exec_first_step by auto
  from a b c d  internal_exec_first_step show ?case 
    using internal_exec.internal_exec_first_step by blast 
   
next
  case (internal_exec_more_steps  \<sigma> tr \<sigma>' \<sigma>'' c)
  from \<open>(link_wf_3M M M' M'') \<Longrightarrow> (M \<circ>\<^bsub>l\<^esub> M'');M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'\<close>
                            and \<open>(link_wf_3M M M' M'')\<close>  
  have a: "(M \<circ>\<^bsub>l\<^esub> M'');M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'" by simp

  have " M\<circ>\<^bsub>l\<^esub> M'' = M''\<circ>\<^bsub>l\<^esub> M "  using \<open>link_wf_3M M M' M''\<close> link_commute by blast
  from this have "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' =  M''\<circ>\<^bsub>l\<^esub> (M \<circ>\<^bsub>l\<^esub> M')" 
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_def link_wf_def 
    by (metis Int_Un_distrib Un_Int_crazy Un_Int_distrib Un_commute distrib_imp2 
        inf.right_idem inf_commute inf_sup_absorb internal_exec_more_steps.prems link_assoc 
        link_commute link_dom link_wf_3M_dest(3) link_wf_3M_dest(4) sup.left_commute sup_assoc 
        sup_bot.left_neutral sup_bot.right_neutral sup_idem sup_inf_distrib1)
  from this have "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub>M''"
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  from this have asm:  "(M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = (M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'" by simp

  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''"
    apply (rule link_exec)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> by blast

  from this and asm  have b: "((M \<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" by simp

  have c: "this_class_lookup \<sigma>'' = Some c \<and> (c \<in> dom (M \<circ>\<^bsub>l\<^esub> M''))"  
    using internal_exec_more_steps by auto

  from a b c internal_exec.internal_exec_more_steps  show ?case  by simp
qed

(*using internal_linking2 to prove the lemma *)
(*Lemma 4.3b: M;M',\<sigma> \<leadsto> \<sigma>'  implies (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<leadsto> \<sigma>'  *)

lemma visible_exec_linking2:
  "\<lbrakk>(M;M',\<sigma> \<leadsto> \<sigma>'); (link_wf_3M M M' M'')\<rbrakk> \<Longrightarrow> (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<leadsto> \<sigma>'"
proof (induction rule: visible_exec.induct)
  case (visible_exec_intro M M' \<sigma> tr \<sigma>' \<sigma>'' c)

  have a: "(M \<circ>\<^bsub>l\<^esub> M'');M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'" using \<open>M;M',\<sigma> \<leadsto>i\<langle>tr\<rangle> \<sigma>'\<close>
    by (simp add: \<open>link_wf_3M M M' M''\<close> internal_linking2)

  have "M \<circ>\<^bsub>l\<^esub> M'' = M'' \<circ>\<^bsub>l\<^esub> M" 
    using link_commute visible_exec_intro by auto
   from this have "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' =  M''\<circ>\<^bsub>l\<^esub> (M \<circ>\<^bsub>l\<^esub> M')" 
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_def link_wf_def by auto
  from this have "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub>M''"
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  from this have asm:  "(M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = (M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'" by simp

    have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''"
    apply (rule link_exec)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> by blast

  from this and asm 
  have b: "((M \<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" by simp

  have c: "this_class_lookup \<sigma>'' = Some c \<and> c \<in> dom M'"
    using \<open>this_class_lookup \<sigma>'' = Some c\<close> and \<open>c \<in> dom M'\<close> by simp 

  from a b c visible_exec.visible_exec_intro show ?case by simp
qed

text \<open>Definition of Initial and Arising configurations\<close>


text \<open>
  For now we assume that the initial stack frame maps no local variables.
  Note that we let the continuation be arbitrary. 
\<close>
definition initial_frame :: "Frame \<Rightarrow> bool" where
"initial_frame \<phi> \<equiv> (vars \<phi> = Map.empty \<and> this \<phi> = Null)"


definition Initial:: "(Stack \<times> Heap) \<Rightarrow> bool" where
"Initial \<sigma> \<equiv> (case \<sigma> of (\<psi>,\<chi>) \<Rightarrow> (case \<psi> of ([\<phi>]) \<Rightarrow> initial_frame \<phi> \<and> \<chi> = Map.empty | _ \<Rightarrow> False))"


inductive exec_module:: "Module \<Rightarrow>Module \<Rightarrow> Config \<Rightarrow> Config \<Rightarrow> bool" ("_;_, _ \<leadsto>* _") where
exec_module_equiv: "\<sigma> = \<sigma>' \<Longrightarrow> M;M', \<sigma> \<leadsto>* \<sigma>'" | 
exec_module_trans: "\<lbrakk> (M;M', \<sigma> \<leadsto>* \<sigma>''); (M; M', \<sigma>'' \<leadsto> \<sigma>')\<rbrakk> \<Longrightarrow> M;M', \<sigma> \<leadsto>* \<sigma>'"


definition Arising:: "Module \<Rightarrow> Module \<Rightarrow> Config set " where
"Arising M M' \<equiv> {\<sigma>.\<exists>\<sigma>\<^sub>0. (Initial \<sigma>\<^sub>0 \<and> (M;M', \<sigma>\<^sub>0 \<leadsto>* \<sigma>))}"


text \<open>Assertions\<close>

text \<open>
  Expressions support nested field lookups, e.g: x.f.g via
  @{text "(EField (EField (EId x) f) g)"}
\<close>
datatype Expr =  ENull |  EId Identifier | EField Expr FieldName

primrec expr_eval :: "Expr \<Rightarrow> Config \<Rightarrow> Value option" where
  "expr_eval ENull \<sigma> = Some (VAddr Null)" |
  "expr_eval (EId x) \<sigma> = evalVar x \<sigma>" |
  "expr_eval (EField e f) \<sigma> = 
     (case (expr_eval e \<sigma>) of Some (VAddr a) \<Rightarrow> 
           field_lookup (snd \<sigma>) a f)"
            

text \<open>
  This returns a @{typ "bool option"} type rather than @{typ bool}?
  For instance, if we are comparing two expressions e and e' and one of them
  evaluates to @{term None}, then the semantics of the comparison is undefined
\<close>
type_synonym Assertion = "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> bool option"

definition
  atrue :: "Assertion"
where
  "atrue  \<equiv> \<lambda>M M' \<sigma>. Some True"


definition
  afalse :: "Assertion"
where
  "afalse  M M' \<sigma> \<equiv> Some False"

term "A  M M' \<sigma>"

text \<open>
  We define generic comparisons between expressions. For example, greater than would
  be expressed as @{text "acompare (>) e e'"}.
\<close>
definition
  acompare :: "(Value \<Rightarrow> Value \<Rightarrow> bool) \<Rightarrow> Expr \<Rightarrow> Expr \<Rightarrow> Assertion"
where
  "acompare c e e' \<equiv> \<lambda>M M' \<sigma>. 
    (case (expr_eval e \<sigma>) of Some v \<Rightarrow>
        (case (expr_eval e' \<sigma>) of Some v' \<Rightarrow> Some (c v v')     
                                | None \<Rightarrow> None)
                           | None \<Rightarrow> None)"

definition 
  bopt  :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option" 
where
  "bopt f a b \<equiv> 
      (case a of Some a' \<Rightarrow> 
          (case b of Some b' \<Rightarrow> Some (f a' b')
                   | None \<Rightarrow> None)
               | None \<Rightarrow> None)"

definition 
  aImp:: " Assertion \<Rightarrow> Assertion \<Rightarrow> Assertion"
where 
   "aImp A A' \<equiv> \<lambda>M M' \<sigma>. bopt (\<longrightarrow>) (A M M' \<sigma>) (A' M M' \<sigma>)"

definition 
  aAnd:: " Assertion \<Rightarrow> Assertion \<Rightarrow> Assertion"
where 
   "aAnd A A' \<equiv> \<lambda>M M' \<sigma>. bopt (\<and>) (A M M' \<sigma>) (A' M M' \<sigma>)"

definition 
  aOr:: " Assertion \<Rightarrow> Assertion \<Rightarrow> Assertion"
where 
   "aOr A A' \<equiv> \<lambda>M M' \<sigma>. bopt (\<or>) (A M M' \<sigma>) (A' M M' \<sigma>)"

definition 
  aNot:: " Assertion  \<Rightarrow> Assertion"
where 
  "aNot A  \<equiv>\<lambda>M M' \<sigma>. case (A M M' \<sigma>) of None \<Rightarrow> None | Some a' \<Rightarrow> Some (\<not> a')"

definition 
  Assert_wf:: "Assertion \<Rightarrow> Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> bool  "
where 
  "Assert_wf A M M' \<sigma>  \<equiv> A M M' \<sigma> \<noteq> None" 


lemma "Assert_wf A M M' \<sigma> 
                \<Longrightarrow> (aAnd A  (aNot A) M M' \<sigma>) = afalse M M' \<sigma>"
  by (simp add: Assert_wf_def aAnd_def aNot_def afalse_def bopt_def option.case_eq_if)

lemma "Assert_wf A M M' \<sigma> 
                \<Longrightarrow> (aOr A  (aNot A) M M' \<sigma>) = atrue M M' \<sigma>"
  by (simp add: Assert_wf_def aNot_def aOr_def atrue_def bopt_def option.case_eq_if)

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aOr A  A' M M' \<sigma>) = (aOr A'  A M M' \<sigma>)"
  unfolding Assert_wf_def aOr_def bopt_def by auto

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aAnd A  A' M M' \<sigma>) = (aAnd A'  A M M' \<sigma>)"
  unfolding Assert_wf_def aAnd_def bopt_def by auto

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aOr (aOr A  A') A''  M M' \<sigma>) = (aOr A (aOr A'  A'')  M M' \<sigma>)"
  unfolding aOr_def bopt_def option.case_eq_if by simp

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma>; Assert_wf A'' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aAnd (aOr A  A') A''  M M' \<sigma>) = (aOr (aAnd A A'') (aAnd A' A'') M M' \<sigma>)"
  unfolding aAnd_def aOr_def bopt_def option.case_eq_if by auto

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma>; Assert_wf A'' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aOr (aAnd A  A') A''  M M' \<sigma>) = (aAnd (aOr A A'') (aOr A' A'') M M' \<sigma>)"
  unfolding aAnd_def aOr_def bopt_def option.case_eq_if by auto

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aNot (aAnd A  A')  M M' \<sigma>) = (aOr (aNot A) (aNot A') M M' \<sigma>)"
  unfolding aAnd_def aOr_def aNot_def bopt_def option.case_eq_if by auto

lemma "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> 
                \<Longrightarrow> (aNot (aOr A  A')  M M' \<sigma>) = (aAnd (aNot A) (aNot A') M M' \<sigma>)"
  unfolding aAnd_def aOr_def aNot_def bopt_def option.case_eq_if by auto 

text \<open>
  A function to return the next visible state, if it exists.
\<close>

definition
  next_visible :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> Config option"
where
  "next_visible M M' \<sigma> \<equiv> 
    if (\<exists>\<sigma>'. (M;M', \<sigma> \<leadsto> \<sigma>')) then Some (THE \<sigma>'. (M;M', \<sigma> \<leadsto> \<sigma>')) else None"

lemma next_visible_SomeI:
  "link_wf M M' \<Longrightarrow> M;M', \<sigma> \<leadsto> \<sigma>' \<Longrightarrow> next_visible M M' \<sigma> = Some \<sigma>'"
  unfolding next_visible_def 
  using the_equality visible_exec_det by metis

lemma next_visible_SomeD:
  "next_visible M M' \<sigma> = Some \<sigma>' \<Longrightarrow> link_wf M M' \<Longrightarrow>
  M;M', \<sigma> \<leadsto> \<sigma>'"
  unfolding next_visible_def
  by (metis next_visible_def next_visible_SomeI option.inject option.simps(3))


text\<open> Next Assertion \<close>

definition 
  Next ::"Assertion \<Rightarrow> Assertion" 
where 
  "Next A   \<equiv> 
   \<lambda>M M' \<sigma>. (case \<sigma> of (\<phi>#_,\<chi>) \<Rightarrow> 
              (case (next_visible M M' ([\<phi>],\<chi>)) of Some \<sigma>' \<Rightarrow> 
                  (case (([\<phi>],\<chi>) \<lhd>  \<sigma>') of 
                     Some adpt \<Rightarrow> (A M M' adpt)| 
                 None \<Rightarrow> None) | 
               None \<Rightarrow> None)  |
                  _  \<Rightarrow> None)"

term "expr_eval S \<sigma> = Some (VAddrSet {a,b,c})"

definition hRst:: "Heap \<Rightarrow> Config \<Rightarrow> Identifier \<Rightarrow> Heap" 
  where 
"hRst \<chi> \<sigma> S  \<equiv> 
     \<lambda>a. (case (evalVar S \<sigma>)  of  
            None \<Rightarrow> None | 
            Some v \<Rightarrow> 
              (case v of VAddr addr \<Rightarrow> None |
                         VAddrSet addrSet \<Rightarrow> if a \<in> addrSet then \<chi> a else None )) "

definition restrictConf :: "Identifier \<Rightarrow> Config \<Rightarrow> Config option"
  where
"restrictConf S \<sigma> \<equiv>  
  (case \<sigma> of (\<psi>, \<chi>) \<Rightarrow> (let \<chi>' = (hRst \<chi> \<sigma> S) in Some (\<psi>, \<chi>')))" 

thm restrictConf_def

term "the (restrictConf \<sigma> S)" 

definition 
  transConf ::"(Config \<Rightarrow> Config option) \<Rightarrow>  Assertion \<Rightarrow> Assertion" 
  where
  "transConf transf A  \<equiv> \<lambda>M M' \<sigma>. (case transf \<sigma> of None \<Rightarrow> None | Some b \<Rightarrow> A M M' b)"

definition 
  In ::"Identifier \<Rightarrow> Assertion \<Rightarrow>  Assertion" 
  where
  "In S \<equiv> transConf (restrictConf S)"


lemma imp_transConf_eq:
  "(aImp (transConf transf A) (transConf transf B) M M' \<sigma>) = 
   (transConf transf (aImp A B)) M M' \<sigma>"
  by (simp add: aImp_def bopt_def option.case_eq_if transConf_def)

(*function for class look_up of expression with \<sigma>
  Class ([e]\<sigma>)\<sigma>
*)

fun
  expr_class_lookup :: "Config \<Rightarrow> Expr \<Rightarrow> ClassName option"
where
  "expr_class_lookup \<sigma> e =  
   (case \<sigma> of (\<phi>#\<psi>,\<chi>) \<Rightarrow>
       (case (expr_eval e \<sigma>) of Some (VAddr a) \<Rightarrow>
            (case \<chi> a of Some obj \<Rightarrow> Some (className obj) |  None \<Rightarrow> None ))
            | _ \<Rightarrow> None)"

text \<open> Basic assertion M; M', \<sigma> \<Turnstile> e : ClassId \<close>

definition
  aExpClassId :: "Expr \<Rightarrow> ClassName \<Rightarrow> Assertion"
where
  "aExpClassId e ClassId \<equiv> \<lambda>M M' \<sigma>. (case (expr_class_lookup \<sigma> e) of None \<Rightarrow> None
                                                                    | Some cid \<Rightarrow> Some (cid = ClassId))" 


text \<open> Viewpoint \<close>
(* 
M; M', \<sigma> \<Turnstile> internal <x> when Class ([x]\<sigma>)\<sigma> \<in> dom M
M; M', \<sigma> \<Turnstile> external <x> when Class ([x]\<sigma>)\<sigma> \<notin> dom M
*)

fun
 Ident_class_lookup :: "Config \<Rightarrow> Identifier \<Rightarrow> ClassName option"
where
  "Ident_class_lookup \<sigma> x =  
   (case \<sigma> of (\<phi>#\<psi>,\<chi>) \<Rightarrow>
       (case (evalVar x \<sigma>) of Some (VAddr a) \<Rightarrow>
            (case \<chi> a of Some obj \<Rightarrow> Some (className obj) |  None \<Rightarrow> None ))
            | _ \<Rightarrow> None)"

definition External:: "Identifier \<Rightarrow> Assertion" 
  where
"External x \<equiv> \<lambda> M M' \<sigma>. (case (Ident_class_lookup \<sigma> x) of None \<Rightarrow> None 
                                             | Some c \<Rightarrow> Some (c \<notin> dom M))"

definition Internal:: "Identifier \<Rightarrow> Assertion"
  where
"Internal x \<equiv> \<lambda> M M' \<sigma>. (case (Ident_class_lookup \<sigma> x) of None \<Rightarrow> None 
                                             | Some c \<Rightarrow> Some (c \<in> dom M))"


text \<open> Basic assertion M; M', \<sigma> \<Turnstile> e \<in> S \<close>

term "(evalVar S \<sigma>)"

(* the function checks [e]\<sigma> \<in> [S]\<sigma> or not *)

fun
  expInS  :: "Config \<Rightarrow> Expr \<Rightarrow> Identifier \<Rightarrow> bool option"
where
  "expInS \<sigma> e S =  
   (case (expr_eval e \<sigma>) of Some (VAddr a) \<Rightarrow>
                 (case (evalVar S \<sigma>) of Some v \<Rightarrow> 
                        (case v of VAddr addr \<Rightarrow> None |
                             VAddrSet addrSet \<Rightarrow> (Some (a \<in> addrSet))) |  
                  None \<Rightarrow> None) | 
            None \<Rightarrow> None)"

(* assertion  M; M', \<sigma> \<Turnstile> e \<in> S with e is an experssion and S is a set  *)

definition 
   aExpInS:: "Expr \<Rightarrow> Identifier \<Rightarrow> Assertion" 
where 
  "aExpInS e S  \<equiv> \<lambda> M M' \<sigma>. (expInS \<sigma> e S)"

text\<open>Permission\<close>

term "this"
term "evalVar x \<sigma>" 

(*
definition of permission: 
M; M', \<sigma> \<Turnstile> <x access y> if [x]\<sigma> and [y]\<sigma> defined,
- [x]\<sigma> = [y]\<sigma> OR
- [x.f]\<sigma> = [y]\<sigma> OR
- [x]\<sigma> = [this]\<sigma> and [y]\<sigma> = [z]\<sigma> 
  for some z and z appear in \<sigma>.contn
*)

(*start thinking of the third case *)

term "Some (VAddr (this \<phi>))"
term "Some (VAddr a)" 
term "this" 

(* the function helps to evaluate [this]\<sigma> *)
fun
  thisEval :: "Config \<Rightarrow> Value option"
where
  "thisEval \<sigma> =  
   (case \<sigma> of (\<phi>#_, _) \<Rightarrow> 
        (case (this \<phi>) of addr \<Rightarrow> Some (VAddr addr))
            | _ \<Rightarrow> None)"

(* 
                AssignToField FieldName Identifier (* this.FieldName := Identifier *) |
                ReadFromField Identifier FieldName (* Identifier := this.Fieldname *) |
                MethodCall    Identifier Identifier MethodName "Identifier list" (*Identifier := Identifier.MethodName(Identifier list) *) |
                NewObject     Identifier ClassName "Identifier list" (*Identifier := new ClassName (Identifier list) *) |
                Return        Identifier (*return Identifier *)
 *)

primrec idents_of_stmt :: "Stmt \<Rightarrow> Identifier set" where
  "idents_of_stmt (AssignToField f v) = {v}" | 
  "idents_of_stmt (ReadFromField v f) = {v}" | 
  "idents_of_stmt (MethodCall v v1 m vs) = {v, v1} \<union> set vs" | 
  "idents_of_stmt (NewObject v c vs) = {v} \<union>  set vs" | 
  "idents_of_stmt (Return v) = {v}"

primrec idents_of_stmts :: "Stmts \<Rightarrow> Identifier set" where
  "idents_of_stmts (SingleStmt s) = idents_of_stmt s" |
  "idents_of_stmts (Seq s ss) = idents_of_stmt s \<union> idents_of_stmts ss"

(*define \<sigma>.cont *)

definition ConfigCont:: "Config \<Rightarrow> Continuation"
  where 
"ConfigCont \<sigma> \<equiv> (case \<sigma> of (\<phi>#_, _) \<Rightarrow> cont \<phi>)"

term "ConfigCont \<sigma>" 

term "\<exists> z y stmts. ((Code stmts =  ConfigCont \<sigma>) \<or> (NestedCall y stmts =  ConfigCont \<sigma>)) \<and>  z \<in>  idents_of_stmts stmts"
term "Code stmts" 
term "cont \<phi>"
(* not finish to define -- todo for than *)

(* not sure about last disjunct
My thinking is exist stmts in Code which is equal to \<sigma>.cont
or NestedCall of any identifier and stmts
from that z \<in> idents_of_stmts stmts *) 

text\<open>Access Assertion\<close>

definition Access:: "Identifier \<Rightarrow> Identifier \<Rightarrow> Assertion"
  where
"Access x y \<equiv> \<lambda>M M' \<sigma>. if (evalVar x \<sigma> = None \<or> evalVar y \<sigma> = None) 
                       then None 
                       else Some ( (evalVar x \<sigma> = evalVar y \<sigma>) \<or> 
                            (\<exists>f. (evalThis f \<sigma> = evalVar y \<sigma>)) \<or> 
                             ((evalVar x \<sigma> = thisEval \<sigma>) \<and> 
                              (\<exists>z z1 stmts. ((Code stmts =  ConfigCont \<sigma>) \<or> (NestedCall z1 stmts =  ConfigCont \<sigma>))
                                    \<and>  (z \<in>  idents_of_stmts stmts) \<and>  (evalVar y \<sigma> = evalVar z \<sigma>) )))"

term "ConfigCont \<sigma> = Code (Seq (MethodCall x u m params) stmts)"

(* definition for [zi]\<sigma> = [vi]\<sigma> for all i  *) 

fun idents_list_equal:: "Identifier list \<Rightarrow> Identifier list \<Rightarrow> Config \<Rightarrow> bool" 
  where 
"idents_list_equal [] [] \<sigma> = True" | 
"idents_list_equal (z#zs) [] \<sigma> = False" | 
"idents_list_equal [] (v#vs) \<sigma> = False" | 
"idents_list_equal (z#zs) (v#vs) \<sigma> = ((evalVar z \<sigma> = evalVar v \<sigma>) \<and> (idents_list_equal zs vs \<sigma>))"

lemma "zs = vs \<Longrightarrow> idents_list_equal zs vs \<sigma>"
  apply (induction rule: idents_list_equal.induct) 
     apply simp+
  done 

(* 
if evalVar z1 \<sigma> = None \<or> ... \<or>  evalVar zn \<sigma> = None
return True 
 *)

fun idents_list_undef:: "Identifier list \<Rightarrow> Config \<Rightarrow> bool"
  where 
"idents_list_undef [] \<sigma> = False" | 
"idents_list_undef (x#xs) \<sigma> = ((evalVar x \<sigma> = None) \<or>  (idents_list_undef xs \<sigma>))"

lemma exist_evalVar_None: "\<exists>  x \<in> set xs. (evalVar x \<sigma> = None) \<Longrightarrow> idents_list_undef xs \<sigma> = True"
  apply (induction rule: idents_list_undef.induct)
    by auto

text\<open>Control Assertion\<close>
definition Calls:: "Identifier \<Rightarrow> Identifier \<Rightarrow> MethodName \<Rightarrow> Identifier list \<Rightarrow> Assertion"
  where
"Calls x y m zs \<equiv> \<lambda>M M' \<sigma>. 
                        if (evalVar x \<sigma> = None \<or> evalVar y \<sigma> = None \<or> (idents_list_undef zs \<sigma>)) 
                        then None 
                        else 
                        Some (( thisEval \<sigma> = evalVar x \<sigma>) \<and> 
                              ( \<exists> a u vs stmts. (ConfigCont \<sigma> = Code (Seq (MethodCall a u m vs) stmts)) \<and> 
                              (evalVar y \<sigma> = evalVar u \<sigma>) \<and> idents_list_equal zs vs \<sigma>))"

text\<open>Changes Assertion\<close>

definition Changes:: "Expr \<Rightarrow> Assertion"
  where 
"Changes e \<equiv>  \<lambda>M M' \<sigma>.  
              (case (next_visible M M' \<sigma>) of Some \<sigma>' \<Rightarrow> 
                  (case (\<sigma> \<lhd> \<sigma>') of Some adpt \<Rightarrow> 
                      (case expr_eval e \<sigma> of Some v1 \<Rightarrow> 
                            (case expr_eval e adpt of Some v2 \<Rightarrow> 
                                     Some (v1 \<noteq> v2) |
                                                        None \<Rightarrow> None ) | 
                                                None \<Rightarrow> None) | 
                                          None \<Rightarrow> None) | 
                                                None \<Rightarrow> None)"

text\<open> Modules satisfying assertion \<close>
term "\<forall>\<sigma>. \<sigma> \<in> Arising M M' "


text\<open>Module satisfying Assertions\<close>

(* TODO: work out what this should say when the assertion is not well defined, i.e. when
         there is some \<sigma> in Arising for which the assertion evaluates to None *)
definition 
  module_sat:: "Module \<Rightarrow> Assertion \<Rightarrow> bool" 
  where
"module_sat M A \<equiv> (\<forall> M' \<sigma>. (\<sigma> \<in> Arising M M') \<longrightarrow> (A M M' \<sigma> = None \<or> A M M' \<sigma> = Some True))"


section \<open> Forall and Exists \<close>

text \<open> Here we use higher order abstract syntax (HOAS) to model these, just like HOAS is
   used to model forall and exists in HOL.
   TODO: we need to find out whether this is sufficient to properly express things like
   \<forall>S:SET. ... etc. \<close>
lemma "(\<forall>x. P x) = (All P)"
  by(rule refl)
term All

definition
  aAll :: "(Identifier \<Rightarrow> Assertion) \<Rightarrow> Assertion"
  where
  "aAll fA \<equiv> \<lambda>M M' \<sigma>. (if (\<exists>v'. fA v' M M' \<sigma> = None) then None
                      else Some (\<forall>v. the (fA v M M' \<sigma>)))" 

text \<open> (\<forall>x. x = x) is equivalent to true, when it is defined \<close>
lemma
  "aAll (\<lambda>x. acompare (=) (EId x) (EId x)) M M' \<sigma> = Some b \<Longrightarrow> b"
  apply(simp add: aAll_def)
  apply(auto split: if_splits option.splits list.splits simp: acompare_def)
  done

definition
  aEx :: "(Identifier \<Rightarrow> Assertion) \<Rightarrow> Assertion"
  where
  "aEx fA \<equiv> \<lambda>M M' \<sigma>. (if (\<exists>v'. fA v' M M' \<sigma> = None) then None
                      else Some (\<exists>v. the (fA v M M' \<sigma>)))"


lemma
  "aEx (\<lambda>x. acompare (=) (EId x) (EId y)) M M' \<sigma> = Some b \<Longrightarrow> b"
  apply(simp add: aEx_def)
  apply(auto split: if_splits option.splits list.splits simp: acompare_def)
  apply (metis option.sel)
  done

section \<open> Some lemmas supporting for proving policies \<close>

(* proof of  (A \<Rightarrow> B) in S  \<equiv> (A in S \<Rightarrow> B in S) *) 

lemma Distrib_In: "(aImp (In S A) (In S B) M M' \<sigma>) = 
       (In S(aImp A B)) M M' \<sigma>"
  using imp_transConf_eq In_def by simp

(* proof of \<not> (A in S) \<equiv> (\<not> A) in S *) 

lemma not_In : "aNot (In S A) M M' \<sigma> = ( In S (aNot A)) M M' \<sigma>"
proof -
  have "\<forall>f fa p fb fc. aNot (transConf fc fb) fa f p = 
          transConf fc (aNot fb) fa f p \<or> fc p = None"
    using aNot_def transConf_def by force
  then show ?thesis
    using In_def aNot_def transConf_def by fastforce
qed

(* \<not>(\<exists>x. A) \<equiv> \<forall>x. (\<not> A) *)
lemma "Assert_wf A M M' \<sigma> \<Longrightarrow>  
          aNot (aEx (\<lambda>x. A  )) M M' \<sigma> = aAll (\<lambda>x. aNot A) M M' \<sigma>"
  unfolding Assert_wf_def aNot_def aEx_def aAll_def 
  by(auto split: option.splits)

(* \<not>(\<forall>x. A) \<equiv> \<exists>x. (\<not> A) *)
lemma "Assert_wf A M M' \<sigma> \<Longrightarrow>  
          aNot (aAll (\<lambda>x. A)) M M' \<sigma> = aEx (\<lambda>x. aNot A) M M' \<sigma>"
  unfolding Assert_wf_def aNot_def aEx_def aAll_def
  using option.case_eq_if option.simps
  by auto

(* (M; M', \<sigma> \<Turnstile> A) \<and> (M; M', \<sigma> \<Turnstile> A \<longrightarrow> A') \<longrightarrow> (M; M', \<sigma> \<Turnstile> A') *)
lemma "Assert_wf A M M' \<sigma> \<Longrightarrow> Assert_wf A' M M' \<sigma>  \<Longrightarrow> 
        (aAnd A (aImp A A'))  M M' \<sigma> = Some True \<Longrightarrow> A' M M' \<sigma> = Some True"
  unfolding Assert_wf_def bopt_def aImp_def aAnd_def aImp_def
  by auto

(* M; M', \<sigma> \<Turnstile> A \<and> \<not> A never holds *)
lemma "Assert_wf A M M' \<sigma> \<Longrightarrow>  
      (aAnd A (aNot A) M M' \<sigma>) = Some False"
  unfolding Assert_wf_def aAnd_def aNot_def bopt_def
  by auto

(* Lemma shows heap unchanged one execution step
\<chi>'(a) = \<chi>(a) when a \<noteq> \<phi>(this) \<and> a \<in> dom \<chi> \<and> \<phi>(this) \<in> dom \<chi> *)

lemma objectUnchanged: 
  "M, \<sigma> \<leadsto> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
  \<forall>a1.((a1 \<noteq> (this \<phi>) \<and> a1 \<in> dom \<chi> \<and> (this \<phi>) \<in> dom \<chi>)\<longrightarrow> \<chi> a1 = \<chi>' a1)"
proof (induction rule: exec.induct)
  case (exec_method_call \<phi> x y m params stmts a \<chi> C paramValues M meth \<phi>'' \<psi>)
  then show ?case by simp
next
  case (exec_var_assign \<phi> x y stmts M \<psi> \<chi>)
  then show ?case by simp
next
  case (exec_field_assign \<phi> y x stmts v \<chi> \<chi>' M \<psi>)
  then show ?case by auto
next
  case (exec_new \<phi> x C params stmts paramValues M c obj' a \<chi> \<chi>' \<psi>) 
  from this have "a \<notin> dom \<chi>" by simp 
  then show ?case using exec_new by fastforce
next                              
  case (exec_return \<phi> x stmts \<phi>' x' stmts' M \<psi> \<chi>)
  then show ?case by simp
qed

(* Lemma shows heap is only changed in field_assign update in one execution step
\<chi>'(\<phi>(this)) = field_update (\<chi> (\<phi>(this)), f, \<phi>(x)) when \<chi>'(\<phi>(this)) \<noteq> \<chi>(\<phi>(this)) *)

lemma objectChanged_FieldAssign: 
  "M, \<sigma> \<leadsto> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
   \<chi>' (this \<phi>) \<noteq> \<chi> (this \<phi>) \<Longrightarrow> (this \<phi>) \<in> dom \<chi> \<Longrightarrow> 
   \<exists>f x. x \<in> dom (vars \<phi>) \<longrightarrow> Some \<chi>'  = this_field_update \<phi> \<chi> f (the (vars \<phi> x))" 
proof (induction rule: exec.induct)
  case (exec_method_call \<phi> x y m params stmts a \<chi> C paramValues M meth \<phi>'' \<psi>)
  then show ?case by simp
next
  case (exec_var_assign \<phi> x y stmts M \<psi> \<chi>)
  then show ?case by simp 
next
  case (exec_field_assign \<phi> y x stmts v \<chi> \<chi>' M \<psi>)
  then show ?case using ident_lookup.elims Pair_inject list.inject option.sel 
    by metis
next
  case (exec_new \<phi> x C params stmts paramValues M c obj' a \<chi> \<chi>' \<psi>)
  from this have "a \<notin> dom \<chi>" by simp
  then show ?case using exec_new by fastforce
next
  case (exec_return \<phi> x stmts \<phi>' x' stmts' M \<psi> \<chi>)
  then show ?case by simp
qed

(* function code return statements s.t
(Code stmts = cont \<phi>) OR  (NestedCall z stmts = cont \<phi>)  *)

fun StmtsCode :: "Frame \<Rightarrow> Stmts"
  where
"StmtsCode \<phi> = (case (cont \<phi>) of (Code stmts) \<Rightarrow> stmts | (NestedCall z stmts) \<Rightarrow> stmts)"

(* do not need the hypothesis that this \<phi> = this \<phi>' *) 
(* the lemma is unprovable *)
(* lemma ident_in_both_code: 
  "M, \<sigma> \<leadsto> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow>
   z \<in> idents_of_stmts (StmtsCode \<phi>') \<Longrightarrow>  z \<in> idents_of_stmts (StmtsCode \<phi>)"
  sorry
*)

end
