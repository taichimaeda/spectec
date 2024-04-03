Modules
-------

.. _binary-typeidx:
.. _binary-funcidx:
.. _binary-tableidx:
.. _binary-memidx:
.. _binary-globalidx:
.. _binary-elemidx:
.. _binary-dataidx:
.. _binary-localidx:
.. _binary-labelidx:
.. _binary-index:

Indices
~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{type index} & \Btypeidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{function index} & \Bfuncidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{table index} & \Btableidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{memory index} & \Bmemidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{global index} & \Bglobalidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{element index} & \Belemidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{data index} & \Bdataidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{local index} & \Blocalidx &::=& x{:}\Bu32 &\Rightarrow& x \\
   \production{label index} & \Blabelidx &::=& l{:}\Bu32 &\Rightarrow& l \\
   \end{array}


.. _binary-section:

Sections
~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad}l}
   \production{section} & \Bsection_N(\B{B}) &::=&
     N{:}\Bbyte~~\X{size}{:}\Bu32~~\X{cont}{:}\B{B}
       &\Rightarrow& \X{cont} & (\iff \X{size} = ||\B{B}||) \\ &&|&
     \epsilon &\Rightarrow& \epsilon
   \end{array}

.. _binary-customsec:

Custom Section
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{custom section} & \Bcustomsec &::=&
     \Bsection_0(\Bcustom) \\
   \production{custom data} & \Bcustom &::=&
     \Bname~~\Bbyte^\ast \\
   \end{array}

.. _binary-typedef:
.. _binary-typesec:

Type Section
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{type section} & \Btypesec &::=&
     \X{ft}^\ast{:\,}\Bsection_1(\Bvec(\Bfunctype)) &\Rightarrow& \X{ft}^\ast \\
   \end{array}


.. _binary-import:
.. _binary-importdesc:
.. _binary-importsec:

Import Section
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{import section} & \Bimportsec &::=&
     \X{im}^\ast{:}\Bsection_2(\Bvec(\Bimport)) &\Rightarrow& \X{im}^\ast \\
   \production{import} & \Bimport &::=&
     \X{mod}{:}\Bname~~\X{nm}{:}\Bname~~d{:}\Bimportdesc
       &\Rightarrow& \{ \IMODULE~\X{mod}, \INAME~\X{nm}, \IDESC~d \} \\
   \production{import description} & \Bimportdesc &::=&
     \hex{00}~~x{:}\Btypeidx &\Rightarrow& \IDFUNC~x \\ &&|&
     \hex{01}~~\X{tt}{:}\Btabletype &\Rightarrow& \IDTABLE~\X{tt} \\ &&|&
     \hex{02}~~\X{mt}{:}\Bmemtype &\Rightarrow& \IDMEM~\X{mt} \\ &&|&
     \hex{03}~~\X{gt}{:}\Bglobaltype &\Rightarrow& \IDGLOBAL~\X{gt} \\
   \end{array}


.. _binary-funcsec:

Function Section
~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{function section} & \Bfuncsec &::=&
     x^\ast{:}\Bsection_3(\Bvec(\Btypeidx)) &\Rightarrow& x^\ast \\
   \end{array}


.. _binary-table:
.. _binary-tablesec:

Table Section
~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{table section} & \Btablesec &::=&
     \X{tab}^\ast{:}\Bsection_4(\Bvec(\Btable)) &\Rightarrow& \X{tab}^\ast \\
   \production{table} & \Btable &::=&
     \X{tt}{:}\Btabletype &\Rightarrow& \{ \TTYPE~\X{tt} \} \\
   \end{array}

.. _binary-mem:
.. _binary-memsec:

Memory Section
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{memory section} & \Bmemsec &::=&
     \X{mem}^\ast{:}\Bsection_5(\Bvec(\Bmem)) &\Rightarrow& \X{mem}^\ast \\
   \production{memory} & \Bmem &::=&
     \X{mt}{:}\Bmemtype &\Rightarrow& \{ \MTYPE~\X{mt} \} \\
   \end{array}

.. _binary-global:
.. _binary-globalsec:

Global Section
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{global section} & \Bglobalsec &::=&
     \X{glob}^\ast{:}\Bsection_6(\Bvec(\Bglobal)) &\Rightarrow& \X{glob}^\ast \\
   \production{global} & \Bglobal &::=&
     \X{gt}{:}\Bglobaltype~~e{:}\Bexpr
       &\Rightarrow& \{ \GTYPE~\X{gt}, \GINIT~e \} \\
   \end{array}

.. _binary-export:
.. _binary-exportdesc:
.. _binary-exportsec:

Export Section
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{export section} & \Bexportsec &::=&
     \X{ex}^\ast{:}\Bsection_7(\Bvec(\Bexport)) &\Rightarrow& \X{ex}^\ast \\
   \production{export} & \Bexport &::=&
     \X{nm}{:}\Bname~~d{:}\Bexportdesc
       &\Rightarrow& \{ \ENAME~\X{nm}, \EDESC~d \} \\
   \production{export description} & \Bexportdesc &::=&
     \hex{00}~~x{:}\Bfuncidx &\Rightarrow& \EDFUNC~x \\ &&|&
     \hex{01}~~x{:}\Btableidx &\Rightarrow& \EDTABLE~x \\ &&|&
     \hex{02}~~x{:}\Bmemidx &\Rightarrow& \EDMEM~x \\ &&|&
     \hex{03}~~x{:}\Bglobalidx &\Rightarrow& \EDGLOBAL~x \\
   \end{array}


.. _binary-start:
.. _binary-startsec:

Start Section
~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{start section} & \Bstartsec &::=&
     \X{st}^?{:}\Bsection_8(\Bstart) &\Rightarrow& \X{st}^? \\
   \production{start function} & \Bstart &::=&
     x{:}\Bfuncidx &\Rightarrow& \{ \SFUNC~x \} \\
   \end{array}


.. _binary-elem:
.. _binary-elemsec:
.. _binary-elemkind:

Element Section
~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{element section} & \Belemsec &::=&
     \X{seg}^\ast{:}\Bsection_9(\Bvec(\Belem)) &\Rightarrow& \X{seg}^\ast \\
   \production{element segment} & \Belem &::=&
     0{:}\Bu32~~e{:}\Bexpr~~y^\ast{:}\Bvec(\Bfuncidx)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~\FUNCREF, \EINIT~((\REFFUNC~y)~\END)^\ast, \EMODE~\EACTIVE~\{ \ETABLE~0, \EOFFSET~e \} \} \\ &&|&
     1{:}\Bu32~~\X{et}:\Belemkind~~y^\ast{:}\Bvec(\Bfuncidx)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~\X{et}, \EINIT~((\REFFUNC~y)~\END)^\ast, \EMODE~\EPASSIVE \} \\ &&|&
     2{:}\Bu32~~x{:}\Btableidx~~e{:}\Bexpr~~\X{et}:\Belemkind~~y^\ast{:}\Bvec(\Bfuncidx)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~\X{et}, \EINIT~((\REFFUNC~y)~\END)^\ast, \EMODE~\EACTIVE~\{ \ETABLE~x, \EOFFSET~e \} \} \\ &&|&
     3{:}\Bu32~~\X{et}:\Belemkind~~y^\ast{:}\Bvec(\Bfuncidx)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~\X{et}, \EINIT~((\REFFUNC~y)~\END)^\ast, \EMODE~\EDECLARATIVE \} \\ &&|&
     4{:}\Bu32~~e{:}\Bexpr~~\X{el}^\ast{:}\Bvec(\Bexpr)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~\FUNCREF, \EINIT~\X{el}^\ast, \EMODE~\EACTIVE~\{ \ETABLE~0, \EOFFSET~e \} \} \\ &&|&
     5{:}\Bu32~~\X{et}:\Breftype~~\X{el}^\ast{:}\Bvec(\Bexpr)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~et, \EINIT~\X{el}^\ast, \EMODE~\EPASSIVE \} \\ &&|&
     6{:}\Bu32~~x{:}\Btableidx~~e{:}\Bexpr~~\X{et}:\Breftype~~\X{el}^\ast{:}\Bvec(\Bexpr)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~et, \EINIT~\X{el}^\ast, \EMODE~\EACTIVE~\{ \ETABLE~x, \EOFFSET~e \} \} \\ &&|&
     7{:}\Bu32~~\X{et}:\Breftype~~\X{el}^\ast{:}\Bvec(\Bexpr)
       &\Rightarrow& \\&&&\quad
       \{ \ETYPE~et, \EINIT~\X{el}^\ast, \EMODE~\EDECLARATIVE \} \\
   \production{element kind} & \Belemkind &::=&
     \hex{00} &\Rightarrow& \FUNCREF \\
   \end{array}

.. _binary-code:
.. _binary-func:
.. _binary-local:
.. _binary-codesec:

Code Section
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad}l}
   \production{code section} & \Bcodesec &::=&
     \X{code}^\ast{:}\Bsection_{10}(\Bvec(\Bcode))
       &\Rightarrow& \X{code}^\ast \\
   \production{code} & \Bcode &::=&
     \X{size}{:}\Bu32~~\X{code}{:}\Bfunc
       &\Rightarrow& \X{code} & (\iff \X{size} = ||\Bfunc||) \\
   \production{function} & \Bfunc &::=&
     (t^\ast)^\ast{:}\Bvec(\Blocals)~~e{:}\Bexpr
       &\Rightarrow& \concat((t^\ast)^\ast), e
         & (\iff |\concat((t^\ast)^\ast)| < 2^{32}) \\
   \production{locals} & \Blocals &::=&
     n{:}\Bu32~~t{:}\Bvaltype &\Rightarrow& t^n \\
   \end{array}

.. _binary-data:
.. _binary-datasec:

Data Section
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{data section} & \Bdatasec &::=&
     \X{seg}^\ast{:}\Bsection_{11}(\Bvec(\Bdata)) &\Rightarrow& \X{seg}^\ast \\
   \production{data segment} & \Bdata &::=&
     0{:}\Bu32~~e{:}\Bexpr~~b^\ast{:}\Bvec(\Bbyte)
       &\Rightarrow& \{ \DINIT~b^\ast, \DMODE~\DACTIVE~\{ \DMEM~0, \DOFFSET~e \} \} \\ &&|&
     1{:}\Bu32~~b^\ast{:}\Bvec(\Bbyte)
       &\Rightarrow& \{ \DINIT~b^\ast, \DMODE~\DPASSIVE \} \\ &&|&
     2{:}\Bu32~~x{:}\Bmemidx~~e{:}\Bexpr~~b^\ast{:}\Bvec(\Bbyte)
       &\Rightarrow& \{ \DINIT~b^\ast, \DMODE~\DACTIVE~\{ \DMEM~x, \DOFFSET~e \} \} \\
   \end{array}

.. _binary-datacountsec:

Data Count Section
~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{data count section} & \Bdatacountsec &::=&
     \X{n}^?{:}\Bsection_{12}(\Bu32) &\Rightarrow& \X{n}^? \\
   \end{array}

.. _binary-magic:
.. _binary-version:
.. _binary-module:

Modules
~~~~~~~

.. math::
   \begin{array}{llcllll}
   \production{magic} & \Bmagic &::=&
     \hex{00}~\hex{61}~\hex{73}~\hex{6D} \\
   \production{version} & \Bversion &::=&
     \hex{01}~\hex{00}~\hex{00}~\hex{00} \\
   \production{module} & \Bmodule &::=&
     \Bmagic \\ &&&
     \Bversion \\ &&&
     \Bcustomsec^\ast \\ &&&
     \functype^\ast{:\,}\Btypesec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \import^\ast{:\,}\Bimportsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \typeidx^n{:\,}\Bfuncsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \table^\ast{:\,}\Btablesec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \mem^\ast{:\,}\Bmemsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \global^\ast{:\,}\Bglobalsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \export^\ast{:\,}\Bexportsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \start^?{:\,}\Bstartsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \elem^\ast{:\,}\Belemsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     m^?{:\,}\Bdatacountsec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \X{code}^n{:\,}\Bcodesec \\ &&&
     \Bcustomsec^\ast \\ &&&
     \data^m{:\,}\Bdatasec \\ &&&
     \Bcustomsec^\ast
     \quad\Rightarrow\quad \{~
       \begin{array}[t]{@{}l@{}}
       \MTYPES~\functype^\ast, \\
       \MFUNCS~\func^n, \\
       \MTABLES~\table^\ast, \\
       \MMEMS~\mem^\ast, \\
       \MGLOBALS~\global^\ast, \\
       \MELEMS~\elem^\ast, \\
       \MDATAS~\data^m, \\
       \MSTART~\start^?, \\
       \MIMPORTS~\import^\ast, \\
       \MEXPORTS~\export^\ast ~\} \\
       \end{array} \\ &&&
     (\iff m^? \neq \epsilon \vee \freedataidx(\X{code}^n) = \emptyset) \\
   \end{array}

where for each :math:`t_i^\ast, e_i` in :math:`\X{code}^n`,

.. math::
   \func^n[i] = \{ \FTYPE~\typeidx^n[i], \FLOCALS~t_i^\ast, \FBODY~e_i \} \\
