.. _binary-type:

Types
-----
.. _binary-numtype:

Number Types
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{number type} & \Bnumtype &::=&
     \hex{7F} &\Rightarrow& \I32 \\ &&|&
     \hex{7E} &\Rightarrow& \I64 \\ &&|&
     \hex{7D} &\Rightarrow& \F32 \\ &&|&
     \hex{7C} &\Rightarrow& \F64 \\
   \end{array}


.. _binary-vectype:

Vector Types
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{vector type} & \Bvectype &::=&
     \hex{7B} &\Rightarrow& \V128 \\
   \end{array}


.. _binary-reftype:

Reference Types
~~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{reference type} & \Breftype &::=&
     \hex{70} &\Rightarrow& \FUNCREF \\ &&|&
     \hex{6F} &\Rightarrow& \EXTERNREF \\
   \end{array}


.. _binary-valtype:

Value Types
~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{value type} & \Bvaltype &::=&
     t{:}\Bnumtype &\Rightarrow& t \\ &&|&
     t{:}\Bvectype &\Rightarrow& t \\ &&|&
     t{:}\Breftype &\Rightarrow& t \\
   \end{array}

.. _binary-resulttype:

Result Types
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{result type} & \Bresulttype &::=&
     t^\ast{:\,}\Bvec(\Bvaltype) &\Rightarrow& [t^\ast] \\
   \end{array}


.. _binary-functype:

Function Types
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{function type} & \Bfunctype &::=&
     \hex{60}~~\X{rt}_1{:\,}\Bresulttype~~\X{rt}_2{:\,}\Bresulttype
       &\Rightarrow& \X{rt}_1 \to \X{rt}_2 \\
   \end{array}

.. _binary-limits:

Limits
~~~~~~

.. math::
   \begin{array}{llclll}
   \production{limits} & \Blimits &::=&
     \hex{00}~~n{:}\Bu32 &\Rightarrow& \{ \LMIN~n, \LMAX~\epsilon \} \\ &&|&
     \hex{01}~~n{:}\Bu32~~m{:}\Bu32 &\Rightarrow& \{ \LMIN~n, \LMAX~m \} \\
   \end{array}

.. _binary-memtype:

Memory Types
~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{memory type} & \Bmemtype &::=&
     \X{lim}{:}\Blimits &\Rightarrow& \X{lim} \\
   \end{array}


.. _binary-tabletype:

Table Types
~~~~~~~~~~~

.. math::
   \begin{array}{llclll}
   \production{table type} & \Btabletype &::=&
     \X{et}{:}\Breftype~~\X{lim}{:}\Blimits &\Rightarrow& \X{lim}~\X{et} \\
   \end{array}


.. _binary-mut:
.. _binary-globaltype:

Global Types
~~~~~~~~~~~~

:ref:`Global types <syntax-globaltype>` are encoded by their :ref:`value type <binary-valtype>` and a flag for their :ref:`mutability <syntax-mut>`.

.. math::
   \begin{array}{llclll}
   \production{global type} & \Bglobaltype &::=&
     t{:}\Bvaltype~~m{:}\Bmut &\Rightarrow& m~t \\
   \production{mutability} & \Bmut &::=&
     \hex{00} &\Rightarrow& \MCONST \\ &&|&
     \hex{01} &\Rightarrow& \MVAR \\
   \end{array}
