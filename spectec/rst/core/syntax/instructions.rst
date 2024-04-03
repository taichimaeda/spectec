.. _syntax-instr:

Instructions
------------

.. _syntax-sx:
.. _syntax-const:
.. _syntax-iunop:
.. _syntax-ibinop:
.. _syntax-itestop:
.. _syntax-irelop:
.. _syntax-funop:
.. _syntax-fbinop:
.. _syntax-ftestop:
.. _syntax-frelop:
.. _syntax-instr-numeric:

Numeric Instructions
~~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{width} & \X{nn}, \X{mm} &::=&
     \K{32} ~|~ \K{64} \\
   \production{signedness} & \sx &::=&
     \K{u} ~|~ \K{s} \\
   \production{instruction} & \instr &::=&
     \K{i}\X{nn}\K{.}\CONST~\xref{syntax/values}{syntax-int}{\uX{\X{nn}}} ~|~
     \K{f}\X{nn}\K{.}\CONST~\xref{syntax/values}{syntax-float}{\fX{\X{nn}}} \\&&|&
     \K{i}\X{nn}\K{.}\iunop ~|~
     \K{f}\X{nn}\K{.}\funop \\&&|&
     \K{i}\X{nn}\K{.}\ibinop ~|~
     \K{f}\X{nn}\K{.}\fbinop \\&&|&
     \K{i}\X{nn}\K{.}\itestop \\&&|&
     \K{i}\X{nn}\K{.}\irelop ~|~
     \K{f}\X{nn}\K{.}\frelop \\&&|&
     \K{i}\X{nn}\K{.}\EXTEND\K{8\_s} ~|~
     \K{i}\X{nn}\K{.}\EXTEND\K{16\_s} ~|~
     \K{i64.}\EXTEND\K{32\_s} \\&&|&
     \K{i32.}\WRAP\K{\_i64} ~|~
     \K{i64.}\EXTEND\K{\_i32}\K{\_}\sx ~|~
     \K{i}\X{nn}\K{.}\TRUNC\K{\_f}\X{mm}\K{\_}\sx \\&&|&
     \K{i}\X{nn}\K{.}\TRUNC\K{\_sat\_f}\X{mm}\K{\_}\sx \\&&|&
     \K{f32.}\DEMOTE\K{\_f64} ~|~
     \K{f64.}\PROMOTE\K{\_f32} ~|~
     \K{f}\X{nn}\K{.}\CONVERT\K{\_i}\X{mm}\K{\_}\sx \\&&|&
     \K{i}\X{nn}\K{.}\REINTERPRET\K{\_f}\X{nn} ~|~
     \K{f}\X{nn}\K{.}\REINTERPRET\K{\_i}\X{nn} \\&&|&
     \dots \\
   \production{integer unary operator} & \iunop &::=&
     \K{clz} ~|~
     \K{ctz} ~|~
     \K{popcnt} \\
   \production{integer binary operator} & \ibinop &::=&
     \K{add} ~|~
     \K{sub} ~|~
     \K{mul} ~|~
     \K{div\_}\sx ~|~
     \K{rem\_}\sx \\&&|&
     \K{and} ~|~
     \K{or} ~|~
     \K{xor} ~|~
     \K{shl} ~|~
     \K{shr\_}\sx ~|~
     \K{rotl} ~|~
     \K{rotr} \\
   \production{floating-point unary operator} & \funop &::=&
     \K{abs} ~|~
     \K{neg} ~|~
     \K{sqrt} ~|~
     \K{ceil} ~|~ 
     \K{floor} ~|~ 
     \K{trunc} ~|~ 
     \K{nearest} \\
   \production{floating-point binary operator} & \fbinop &::=&
     \K{add} ~|~
     \K{sub} ~|~
     \K{mul} ~|~
     \K{div} ~|~
     \K{min} ~|~
     \K{max} ~|~
     \K{copysign} \\
   \production{integer test operator} & \itestop &::=&
     \K{eqz} \\
   \production{integer relational operator} & \irelop &::=&
     \K{eq} ~|~
     \K{ne} ~|~
     \K{lt\_}\sx ~|~
     \K{gt\_}\sx ~|~
     \K{le\_}\sx ~|~
     \K{ge\_}\sx \\
   \production{floating-point relational operator} & \frelop &::=&
     \K{eq} ~|~
     \K{ne} ~|~
     \K{lt} ~|~
     \K{gt} ~|~
     \K{le} ~|~
     \K{ge} \\
   \end{array}

.. _syntax-unop:
.. _syntax-binop:
.. _syntax-testop:
.. _syntax-relop:
.. _syntax-cvtop:

Conventions
...........

Occasionally, it is convenient to group operators together according to the following grammar shorthands:

.. math::
   \begin{array}{llll}
   \production{unary operator} & \unop &::=&
     \iunop ~|~
     \funop ~|~
     \EXTEND{N}\K{\_s} \\
   \production{binary operator} & \binop &::=& \ibinop ~|~ \fbinop \\
   \production{test operator} & \testop &::=& \itestop \\
   \production{relational operator} & \relop &::=& \irelop ~|~ \frelop \\
   \production{conversion operator} & \cvtop &::=&
     \WRAP ~|~
     \EXTEND ~|~
     \TRUNC ~|~
     \TRUNC\K{\_sat} ~|~
     \CONVERT ~|~
     \DEMOTE ~|~
     \PROMOTE ~|~
     \REINTERPRET \\
   \end{array}


.. _syntax-laneidx:
.. _syntax-shape:
.. _syntax-half:
.. _syntax-vvunop:
.. _syntax-vvbinop:
.. _syntax-vvternop:
.. _syntax-vvtestop:
.. _syntax-vitestop:
.. _syntax-virelop:
.. _syntax-vfrelop:
.. _syntax-vishiftop:
.. _syntax-viunop:
.. _syntax-vibinop:
.. _syntax-viminmaxop:
.. _syntax-visatbinop:
.. _syntax-vfunop:
.. _syntax-vfbinop:
.. _syntax-instr-vec:


Vector Instructions
~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{ishape} & \ishape &::=&
     \K{i8x16} ~|~ \K{i16x8} ~|~ \K{i32x4} ~|~ \K{i64x2} \\
   \production{fshape} & \fshape &::=&
     \K{f32x4} ~|~ \K{f64x2} \\
   \production{shape} & \shape &::=&
     \ishape ~|~ \fshape \\
   \production{half} & \half &::=&
     \K{low} ~|~ \K{high} \\
   \production{lane index} & \laneidx &::=& \u8 \\
   \end{array}

.. math::
   \begin{array}{llcl}
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \K{v128.}\VCONST~\i128 \\&&|&
     \K{v128.}\vvunop \\&&|&
     \K{v128.}\vvbinop \\&&|&
     \K{v128.}\vvternop \\&&|&
     \K{v128.}\vvtestop \\&&|&
     \K{i8x16.}\SHUFFLE~\laneidx^{16} \\&&|&
     \K{i8x16.}\SWIZZLE \\&&|&
     \shape\K{.}\SPLAT \\&&|&
     \K{i8x16.}\EXTRACTLANE\K{\_}\sx~\laneidx ~|~
     \K{i16x8.}\EXTRACTLANE\K{\_}\sx~\laneidx \\&&|&
     \K{i32x4.}\EXTRACTLANE~\laneidx ~|~
     \K{i64x2.}\EXTRACTLANE~\laneidx \\&&|&
     \fshape\K{.}\EXTRACTLANE~\laneidx \\&&|&
     \shape\K{.}\REPLACELANE~\laneidx \\&&|&
     \K{i8x16}\K{.}\virelop ~|~
     \K{i16x8}\K{.}\virelop ~|~
     \K{i32x4}\K{.}\virelop \\&&|&
     \K{i64x2.}\K{eq} ~|~
     \K{i64x2.}\K{ne} ~|~
     \K{i64x2.}\K{lt\_s} ~|~
     \K{i64x2.}\K{gt\_s} ~|~
     \K{i64x2.}\K{le\_s} ~|~
     \K{i64x2.}\K{ge\_s} \\&&|&
     \fshape\K{.}\vfrelop \\&&|&
     \ishape\K{.}\viunop ~|~
     \K{i8x16.}\VPOPCNT \\&&|&
     \K{i16x8.}\Q15MULRSAT\K{\_s} \\ &&|&
     \K{i32x4.}\DOT\K{\_i16x8\_s} \\ &&|&
     \fshape\K{.}\vfunop \\&&|&
     \ishape\K{.}\vitestop \\ &&|&
     \ishape\K{.}\BITMASK \\ &&|&
     \K{i8x16.}\NARROW\K{\_i16x8\_}\sx ~|~
     \K{i16x8.}\NARROW\K{\_i32x4\_}\sx \\&&|&
     \K{i16x8.}\VEXTEND\K{\_}\half\K{\_i8x16\_}\sx ~|~
     \K{i32x4.}\VEXTEND\K{\_}\half\K{\_i16x8\_}\sx \\&&|&
     \K{i64x2.}\VEXTEND\K{\_}\half\K{\_i32x4\_}\sx \\&&|&
     \ishape\K{.}\vishiftop \\&&|&
     \ishape\K{.}\vibinop \\&&|&
     \K{i8x16.}\viminmaxop ~|~
     \K{i16x8.}\viminmaxop ~|~
     \K{i32x4.}\viminmaxop \\&&|&
     \K{i8x16.}\visatbinop ~|~
     \K{i16x8.}\visatbinop \\&&|&
     \K{i16x8.}\K{mul} ~|~
     \K{i32x4.}\K{mul} ~|~
     \K{i64x2.}\K{mul} \\&&|&
     \K{i8x16.}\AVGR\K{\_u} ~|~
     \K{i16x8.}\AVGR\K{\_u} \\&&|&
     \K{i16x8.}\EXTMUL\K{\_}\half\K{\_i8x16\_}\sx ~|~
     \K{i32x4.}\EXTMUL\K{\_}\half\K{\_i16x8\_}\sx ~|~
     \K{i64x2.}\EXTMUL\K{\_}\half\K{\_i32x4\_}\sx \\ &&|&
     \K{i16x8.}\EXTADDPAIRWISE\K{\_i8x16\_}\sx ~|~
     \K{i32x4.}\EXTADDPAIRWISE\K{\_i16x8\_}\sx \\ &&|&
     \fshape\K{.}\vfbinop \\&&|&
     \K{i32x4.}\VTRUNC\K{\_sat\_f32x4\_}\sx ~|~
     \K{i32x4.}\VTRUNC\K{\_sat\_f64x2\_}\sx\K{\_zero} \\&&|&
     \K{f32x4.}\VCONVERT\K{\_i32x4\_}\sx ~|~
     \K{f32x4.}\VDEMOTE\K{\_f64x2\_zero} \\&&|&
     \K{f64x2.}\VCONVERT\K{\_low\_i32x4\_}\sx ~|~
     \K{f64x2.}\VPROMOTE\K{\_low\_f32x4} \\&&|&
     \dots \\
   \end{array}

.. math::
   \begin{array}{llcl}
   \production{vector bitwise unary operator} & \vvunop &::=&
     \K{not} \\
   \production{vector bitwise binary operator} & \vvbinop &::=&
     \K{and} ~|~
     \K{andnot} ~|~
     \K{or} ~|~
     \K{xor} \\
   \production{vector bitwise ternary operator} & \vvternop &::=&
     \K{bitselect} \\
   \production{vector bitwise test operator} & \vvtestop &::=&
     \K{any\_true} \\
   \production{vector integer test operator} & \vitestop &::=&
     \K{all\_true} \\
   \production{vector integer relational operator} & \virelop &::=&
     \K{eq} ~|~
     \K{ne} ~|~
     \K{lt\_}\sx ~|~
     \K{gt\_}\sx ~|~
     \K{le\_}\sx ~|~
     \K{ge\_}\sx \\
   \production{vector floating-point relational operator} & \vfrelop &::=&
     \K{eq} ~|~
     \K{ne} ~|~
     \K{lt} ~|~
     \K{gt} ~|~
     \K{le} ~|~
     \K{ge} \\
   \production{vector integer unary operator} & \viunop &::=&
     \K{abs} ~|~
     \K{neg} \\
   \production{vector integer binary operator} & \vibinop &::=&
     \K{add} ~|~
     \K{sub} \\
   \production{vector integer binary min/max operator} & \viminmaxop &::=&
     \K{min\_}\sx ~|~
     \K{max\_}\sx \\
   \production{vector integer saturating binary operator} & \visatbinop &::=&
     \K{add\_sat\_}\sx ~|~
     \K{sub\_sat\_}\sx \\
   \production{vector integer shift operator} & \vishiftop &::=&
     \K{shl} ~|~
     \K{shr\_}\sx \\
   \production{vector floating-point unary operator} & \vfunop &::=&
     \K{abs} ~|~
     \K{neg} ~|~
     \K{sqrt} ~|~
     \K{ceil} ~|~
     \K{floor} ~|~
     \K{trunc} ~|~
     \K{nearest} \\
   \production{vector floating-point binary operator} & \vfbinop &::=&
     \K{add} ~|~
     \K{sub} ~|~
     \K{mul} ~|~
     \K{div} ~|~
     \K{min} ~|~
     \K{max} ~|~
     \K{pmin} ~|~
     \K{pmax} \\
   \end{array}

.. _syntax-vec-shape:
.. _syntax-vunop:
.. _syntax-vbinop:
.. _syntax-vrelop:
.. _syntax-vtestop:
.. _syntax-vcvtop:

Conventions
...........

Occasionally, it is convenient to group operators together according to the following grammar shorthands:

.. math::
   \begin{array}{llll}
   \production{unary operator} & \vunop &::=&
     \viunop ~|~
     \vfunop ~|~
     \VPOPCNT \\
   \production{binary operator} & \vbinop &::=&
     \vibinop ~|~ \vfbinop \\&&|&
     \viminmaxop ~|~ \visatbinop \\&&|&
     \VMUL ~|~
     \AVGR\K{\_u} ~|~
     \Q15MULRSAT\K{\_s} \\
   \production{test operator} & \vtestop &::=&
     \vitestop \\
   \production{relational operator} & \vrelop &::=&
     \virelop ~|~ \vfrelop \\
   \production{conversion operator} & \vcvtop &::=&
     \VEXTEND ~|~
     \VTRUNC\K{\_sat} ~|~
     \VCONVERT ~|~
     \VDEMOTE ~|~
     \VPROMOTE \\
   \end{array}

.. _syntax-ref.null:
.. _syntax-ref.is_null:
.. _syntax-ref.func:
.. _syntax-instr-ref:


Reference Instructions
~~~~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \REFNULL~\reftype \\&&|&
     \REFISNULL \\&&|&
     \REFFUNC~\funcidx \\
   \end{array}

.. _syntax-instr-parametric:

Parametric Instructions
~~~~~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \DROP \\&&|&
     \SELECT~(\valtype^\ast)^? \\
   \end{array}

.. _syntax-instr-variable:

Variable Instructions
~~~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \LOCALGET~\localidx \\&&|&
     \LOCALSET~\localidx \\&&|&
     \LOCALTEE~\localidx \\&&|&
     \GLOBALGET~\globalidx \\&&|&
     \GLOBALSET~\globalidx \\
   \end{array}

.. _syntax-instr-table:
.. _syntax-table.get:
.. _syntax-table.set:
.. _syntax-table.size:
.. _syntax-table.grow:
.. _syntax-table.fill:

Table Instructions
~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \TABLEGET~\tableidx \\&&|&
     \TABLESET~\tableidx \\&&|&
     \TABLESIZE~\tableidx \\&&|&
     \TABLEGROW~\tableidx \\&&|&
     \TABLEFILL~\tableidx \\&&|&
     \TABLECOPY~\tableidx~\tableidx \\&&|&
     \TABLEINIT~\tableidx~\elemidx \\&&|&
     \ELEMDROP~\elemidx \\
   \end{array}

.. _syntax-loadn:
.. _syntax-storen:
.. _syntax-memarg:
.. _syntax-lanewidth:
.. _syntax-instr-memory:

Memory Instructions
~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{memory immediate} & \memarg &::=&
     \{ \OFFSET~\u32, \ALIGN~\u32 \} \\
   \production{lane width} & \X{ww} &::=&
     8 ~|~ 16 ~|~ 32 ~|~ 64 \\
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \K{i}\X{nn}\K{.}\LOAD~\memarg ~|~
     \K{f}\X{nn}\K{.}\LOAD~\memarg ~|~
     \K{i}\X{nn}\K{.}\STORE~\memarg ~|~
     \K{f}\X{nn}\K{.}\STORE~\memarg ~|~
     \K{i}\X{nn}\K{.}\LOAD\K{8\_}\sx~\memarg ~|~
     \K{i}\X{nn}\K{.}\LOAD\K{16\_}\sx~\memarg ~|~
     \K{i64.}\LOAD\K{32\_}\sx~\memarg \\&&|&
     \K{i}\X{nn}\K{.}\STORE\K{8}~\memarg ~|~
     \K{i}\X{nn}\K{.}\STORE\K{16}~\memarg ~|~
     \K{i64.}\STORE\K{32}~\memarg \\&&|&
     \MEMORYSIZE \\&&|&
     \MEMORYGROW \\&&|&
     \MEMORYFILL \\&&|&
     \MEMORYCOPY \\&&|&
     \MEMORYINIT~\dataidx \\&&|&
     \DATADROP~\dataidx \\
   \end{array}

.. _syntax-blocktype:
.. _syntax-nop:
.. _syntax-unreachable:
.. _syntax-block:
.. _syntax-loop:
.. _syntax-if:
.. _syntax-br:
.. _syntax-br_if:
.. _syntax-br_table:
.. _syntax-return:
.. _syntax-call:
.. _syntax-call_indirect:
.. _syntax-instr-seq:
.. _syntax-instr-control:

Control Instructions
~~~~~~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llcl}
   \production{block type} & \blocktype &::=&
     \typeidx ~|~ \valtype^? \\
   \production{instruction} & \instr &::=&
     \dots \\&&|&
     \NOP \\&&|&
     \UNREACHABLE \\&&|&
     \BLOCK~\blocktype~\instr^\ast~\END \\&&|&
     \LOOP~\blocktype~\instr^\ast~\END \\&&|&
     \IF~\blocktype~\instr^\ast~\ELSE~\instr^\ast~\END \\&&|&
     \BR~\labelidx \\&&|&
     \BRIF~\labelidx \\&&|&
     \BRTABLE~\vec(\labelidx)~\labelidx \\&&|&
     \RETURN \\&&|&
     \CALL~\funcidx \\&&|&
     \CALLINDIRECT~\tableidx~\typeidx \\
   \end{array}

.. _syntax-expr:

Expressions
~~~~~~~~~~~

.. math::
   \begin{array}{llll}
   \production{expression} & \expr &::=&
     \instr^\ast~\END \\
   \end{array}
