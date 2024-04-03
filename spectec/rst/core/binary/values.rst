.. _binary-value:

Values
------

.. _binary-byte:

Bytes
~~~~~

.. math::
   \begin{array}{llcll@{\qquad}l}
   \production{byte} & \Bbyte &::=&
     \hex{00} &\Rightarrow& \hex{00} \\ &&|&&
     \dots \\ &&|&
     \hex{FF} &\Rightarrow& \hex{FF} \\
   \end{array}


.. _binary-sint:
.. _binary-uint:
.. _binary-int:

Integers
~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad}l}
   \production{unsigned integer} & \BuN &::=&
     n{:}\Bbyte &\Rightarrow& n & (\iff n < 2^7 \wedge n < 2^N) \\ &&|&
     n{:}\Bbyte~~m{:}\BuX{(N\B{-7})} &\Rightarrow&
       2^7\cdot m + (n-2^7) & (\iff n \geq 2^7 \wedge N > 7) \\
   \end{array}

.. math::
   \begin{array}{llclll@{\qquad}l}
   \production{signed integer} & \BsN &::=&
     n{:}\Bbyte &\Rightarrow& n & (\iff n < 2^6 \wedge n < 2^{N-1}) \\ &&|&
     n{:}\Bbyte &\Rightarrow& n-2^7 & (\iff 2^6 \leq n < 2^7 \wedge n \geq 2^7-2^{N-1}) \\ &&|&
     n{:}\Bbyte~~m{:}\BsX{(N\B{-7})} &\Rightarrow&
       2^7\cdot m + (n-2^7) & (\iff n \geq 2^7 \wedge N > 7) \\
   \end{array}

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{uninterpreted integer} & \BiN &::=&
     n{:}\BsN &\Rightarrow& i & (\iff n = \signed_N(i))
   \end{array}

.. _binary-float:

Floating-Point
~~~~~~~~~~~~~~

.. math::
   \begin{array}{llclll@{\qquad\qquad}l}
   \production{floating-point value} & \BfN &::=&
     b^\ast{:\,}\Bbyte^{N/8} &\Rightarrow& \bytes_{\fN}^{-1}(b^\ast) \\
   \end{array}


.. _binary-utf8:
.. _binary-name:

Names
~~~~~

.. math::
   \begin{array}{llclllll}
   \production{name} & \Bname &::=&
     b^\ast{:}\Bvec(\Bbyte) &\Rightarrow& \name
       && (\iff \utf8(\name) = b^\ast) \\
   \end{array}

.. math::
   \begin{array}{@{}l@{}}
   \begin{array}{@{}lcl@{\qquad}l@{}}
   \utf8(c^\ast) &=& (\utf8(c))^\ast \\[1ex]
   \utf8(c) &=& b &
     (\begin{array}[t]{@{}c@{~}l@{}}
      \iff & c < \unicode{80} \\
      \wedge & c = b) \\
      \end{array} \\
   \utf8(c) &=& b_1~b_2 &
     (\begin{array}[t]{@{}c@{~}l@{}}
      \iff & \unicode{80} \leq c < \unicode{800} \\
      \wedge & c = 2^6(b_1-\hex{C0})+(b_2-\hex{80})) \\
      \end{array} \\
   \utf8(c) &=& b_1~b_2~b_3 &
     (\begin{array}[t]{@{}c@{~}l@{}}
      \iff & \unicode{800} \leq c < \unicode{D800} \vee \unicode{E000} \leq c < \unicode{10000} \\
      \wedge & c = 2^{12}(b_1-\hex{E0})+2^6(b_2-\hex{80})+(b_3-\hex{80})) \\
      \end{array} \\
   \utf8(c) &=& b_1~b_2~b_3~b_4 &
     (\begin{array}[t]{@{}c@{~}l@{}}
      \iff & \unicode{10000} \leq c < \unicode{110000} \\
      \wedge & c = 2^{18}(b_1-\hex{F0})+2^{12}(b_2-\hex{80})+2^6(b_3-\hex{80})+(b_4-\hex{80})) \\
      \end{array} \\
   \end{array} \\
   \where b_2, b_3, b_4 < \hex{C0} \\
   \end{array}
