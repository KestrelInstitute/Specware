

========
Inbuilts
========

.. COMMENT:  <appendix><title>Inbuilts and Base Libraries</title> 

This appendix provides a brief description of the "inbuilt" types and
operators.

.. COMMENT: <para>
            This appendix provides a brief description of the types and operators
            that are either "inbuilt" or provided by the current base libraries.
            The base libraries are automatically imported by every user-defined :token:`spec`.
            The title of each section of this appendix
            is the qualifier of the :token:`type_` and :token:`op_names` given therein.
            For example, the full :token:`name` for :token:`op` ``++`` described
            in Section "List" is ``List.++``\ .
            However, for the <emphasis>unary</emphasis> operator ``-`` on integers,
            the qualifier is ``Integer_`` .
            Note, also, that inbuilts cannot be qualified.
            </para>

For the sake of brevity, ``infixl`` is abbreviated below to ``L`` and
``infixr`` to ``R``\ .

.. COMMENT: <para>
            See the actual base library ``.sw`` files, provided
            with the |Specware| distribution, for details (e.g. axioms).
            </para>

.. COMMENT:  Inbuilts ****************************************************** 

.. COMMENT:  <section><title>Inbuilts</title> 
  :command:`Inbuilt Type`
    \ ``Bool``\

  :command:`Inbuilt Ops`
  .. list-table::
       :widths: 65 41 150 160
       :header-rows: 1
       *  - |nbsp| Name
          - |nbsp| Fixity
          - |nbsp| Type
          - |nbsp| Description
       *  - |nbsp| ``=``\
          - |nbsp| ``R 20``\
          - |nbsp| ``[a] a * a -> Bool``\
          - |nbsp| tests if the parameters are equal
       *  - |nbsp| ``~=``\
          - |nbsp| ``R 20``\
          - |nbsp| ``[a] a * a -> Bool``\
          - |nbsp| tests if the parameters are unequal
       *  - |nbsp| ``~``\
          - |nbsp|
          - |nbsp| ``Bool -> Bool``\
          - |nbsp| logical negation
       *  - |nbsp| ``&&``\
          - |nbsp| ``R 15``\
          - |nbsp| ``Bool * Bool -> Bool``\
          - |nbsp| non-strict logical and
       *  - |nbsp| ``||``\
          - |nbsp| ``R 14``\
          - |nbsp| ``Bool * Bool -> Bool``\
          - |nbsp| non-strict logical or
       *  - |nbsp| ``=>``\
          - |nbsp| ``R 13``\
          - |nbsp| ``Bool * Bool -> Bool``\
          - |nbsp| non-strict logical implication
       *  - |nbsp| ``<=>``\
          - |nbsp| ``R 12``\
          - |nbsp| ``Bool * Bool -> Bool``\
          - |nbsp| logical equivalence
       *  - |nbsp| ``<<``\
          - |nbsp| ``L 25``\
          - |nbsp| ``{``\ *x*\ ``:``\ *A*\ ``,``\ ...\ ``,``\ *y*\ ``:``\
            *B*\ ``,``\ ...\ ``} * {``\ *x*\ ``:``\ *A*\ ``,``\ ...\
            ``,``\ *z*\ ``:``\ *C*\ ``,``\ ...\ ``} -> {``\ *x*\ ``:``\
            *A*\ ``,``\ ...\ ``,``\ *y*\ ``:``\ *B*\ ``,``\ ...\ ``,``\
            *z*\ ``:``\ *C*\ ``,``\ ...\ ``}``\
          - |nbsp| see Section :token:`Applications` under
 

.. COMMENT:  </section> 

.. COMMENT:  Bool ****************************************************** 

.. COMMENT: <section><title>Bool</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                  <informaltable frame="sides" colsep="1">
                   <tgroup cols="4">
                    <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                    <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                    <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                    <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                    <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                    </thead>
                    <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``toString``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Bool -> String``\ </entry>
                    <entry colname="desc">|nbsp| converts logical value to string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Bool -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``toString``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Bool * Bool -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| compares two logical values</entry>
                   </row>
                    </tbody>
                   </tgroup>
                  </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  Integer ****************************************************** 

.. COMMENT: <section><title>Integer</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Types</command></term>
                <listitem><para>\ ``type Integer``\ </para>
                          <para>\ ``type NonZeroInteger = {i : Integer | i ~= 0}``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                  <informaltable frame="sides" colsep="1">
                   <tgroup cols="4">
                    <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                    <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                    <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                    <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                    <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                    </thead>
                    <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``-``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| unary minus (has :token:`qualifier` ``Integer_``\ !)</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``+``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 25``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| addition</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``-``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 25``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| subtraction</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``*``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 27``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| multiplication</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``div``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 26``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * NonZeroInteger -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| division (truncates towards 0)</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``rem``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 26``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * NonZeroInteger -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| remainder (\ \ *x*\  ``rem``\ *y*\  ``=``\ *x*\  ``-``\ *y*\  ``* (``\ *x*\  ``div``\ *y*\ ``)``\ )</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``<``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 20``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| less-than</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``&lt;=``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 20``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| less-than-or-equal</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``>``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 20``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| greater-than</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``>=``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 20``\ </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| greater-than-or-equal</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``abs``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer -> Nat``\ </entry>
                    <entry colname="desc">|nbsp| absolute value</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``min``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| minimum</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``max``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| maximum</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer * Integer -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| compares two integers</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``toString``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer -> String``\ </entry>
                    <entry colname="desc">|nbsp| converts integer to string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``toString``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``intToString``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Integer -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``toString``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``intConvertible``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| tests if string is representation of integer</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``stringToInt``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``(String | intConvertible) -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| converts "convertible" string to integer</entry>
                   </row>
                    </tbody>
                   </tgroup>
                  </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  Nat ****************************************************** 

.. COMMENT: <section><title>Nat</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Types</command></term>
                <listitem><para>\ ``type Nat = {n : Integer | n >= 0}``\ </para>
                          <para>\ ``type PosNat = {n : Nat | n &lt; 0 }``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                  <informaltable frame="sides" colsep="1">
                   <tgroup cols="4">
                    <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                    <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                    <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                    <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                    <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                    </thead>
                    <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``succ``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> Nat``\ </entry>
                    <entry colname="desc">|nbsp| successor</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``pred``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> Integer``\ </entry>
                    <entry colname="desc">|nbsp| predecessor</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``zero``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat``\ </entry>
                    <entry colname="desc">|nbsp| the natural number 0</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``one``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat``\ </entry>
                    <entry colname="desc">|nbsp| the natural number 1</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``two``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat``\ </entry>
                    <entry colname="desc">|nbsp| the natural number 2</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``posNat?``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| yields false for 0, true otherwise</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``toString``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> String``\ </entry>
                    <entry colname="desc">|nbsp| 
                        converts natural number to string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``toString``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``natToString``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``toString``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``natConvertible``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| tests if string is representation of natural number</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``stringToNat``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``(String | natConvertible) -> Nat``\ </entry>
                    <entry colname="desc">|nbsp| converts "convertible" string to natural number</entry>
                   </row>
                    </tbody>
                   </tgroup>
                  </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  Char ****************************************************** 

.. COMMENT: <section><title>Char</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Type</command></term>
                <listitem><para>\ ``type Char``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                  <informaltable frame="sides" colsep="1">
                   <tgroup cols="4">
                    <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                    <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                    <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                    <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                    <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                    </thead>
                    <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``ord``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Nat``\ </entry>
                    <entry colname="desc">|nbsp| converts character to natural number</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``chr``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Nat -> Char``\ </entry>
                    <entry colname="desc">|nbsp| converts natural number to character</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``isAlpha``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for letters</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``isNum``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for digits</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``isAlphaNum``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for letters and digits</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``isAscii``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for ASCII characters</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``isLowerCase``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for lower-case letters</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``isUpperCase``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for upper-case letters</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``toUpperCase``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Char``\ </entry>
                    <entry colname="desc">|nbsp| converts to upper case</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``toLowerCase``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> Char``\ </entry>
                    <entry colname="desc">|nbsp| converts to lower case</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char * Char -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| compares two character values</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``toString``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> String``\ </entry>
                    <entry colname="desc">|nbsp| converts character to string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Char -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``toString``\ </entry>
                   </row>
                    </tbody>
                   </tgroup>
                  </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  String ****************************************************** 

.. COMMENT: <section><title>String</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Type</command></term>
                <listitem><para>\ ``type String``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                  <informaltable frame="sides" colsep="1">
                   <tgroup cols="4">
                    <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                    <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                    <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                    <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                    <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                    </thead>
                    <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``explode``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String -> List(Char)``\ </entry>
                    <entry colname="desc">|nbsp| converts string to list of characters</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``implode``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``List(Char) -> String``\ </entry>
                    <entry colname="desc">|nbsp| converts list of characters to string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``length``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String -> Nat``\ </entry>
                    <entry colname="desc">|nbsp| length of a string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``leq``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 20``\ </entry>
                    <entry colname="type">|nbsp| ``String * String -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| lexicographic less-than-or-equal</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``lt``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 20``\ </entry>
                    <entry colname="type">|nbsp| ``String * String -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| lexicographic less-than</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``^``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 25``\ </entry>
                    <entry colname="type">|nbsp| ``String * String -> String``\ </entry>
                    <entry colname="desc">|nbsp| same as ``++``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``concat``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String * String -> String``\ </entry>
                    <entry colname="desc">|nbsp| prefix :token:`op` for string concatenation</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``concatList``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``List String -> String``\ </entry>
                    <entry colname="desc">|nbsp| returns the concatenation of the list elements</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``sub``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String * Nat -> Char``\ </entry>
                    <entry colname="desc">|nbsp| returns the *n*th character in a string, counting from 0</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``substring``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String * Nat * Nat -> String``\ </entry>
                    <entry colname="desc">|nbsp| ``substring(``\ *s*\ ``,``\ *m*\ ``,``\ *n*\ ``)`` returns the substring of
                        *s* from position *m* through position
                        \ *n*\ ``-1``\ , counting from 0</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``map``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``(Char -> Char) * String -> String``\ </entry>
                    <entry colname="desc">|nbsp| returns the concatenation of the results of applying the
                        function given as first parameter to each character of the string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``translate``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``(Char -> String) * String -> String``\ </entry>
                    <entry colname="desc">|nbsp| returns the concatenation of the results of applying the
                        function given as first parameter to each character of the string</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``all``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``(Char -> Bool) * String``\ </entry>
                    <entry colname="desc">|nbsp| true if all characters in the string satisfy
                        the predicate given as first parameter</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``exists``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``(Char -> Bool) * String``\ </entry>
                    <entry colname="desc">|nbsp| true if some character in the string satisfies
                        the predicate given as first parameter</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``newline``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String``\ </entry>
                    <entry colname="desc">|nbsp| the string representing a line break</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``toScreen``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String -> ()``\ </entry>
                    <entry colname="desc">|nbsp| prints the string on the terminal</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``writeLine``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String -> ()``\ </entry>
                    <entry colname="desc">|nbsp| same with a newline appended</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``String * String -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| compares two strings</entry>
                   </row>
                    </tbody>
                   </tgroup>
                  </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  List ****************************************************** 

.. COMMENT: <section><title>List</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Type</command></term>
                <listitem><para>\ ``type List a = | Nil | Cons a * List a``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                  <informaltable frame="sides" colsep="1">
                   <tgroup cols="4">
                    <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                    <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                    <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                    <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                    <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                    </thead>
                    <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``nil``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a``\ </entry>
                    <entry colname="desc">|nbsp| the empty list</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``null``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true for empty lists</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``length``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``List a -> Nat``\ </entry>
                    <entry colname="desc">|nbsp| length of a list</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``cons``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] a * List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| constructs a list consisting of a first element and a
                        list tail</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``insert``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] a * List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| same as ``cons``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``hd``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a -> a``\ </entry>
                    <entry colname="desc">|nbsp| returns the first element of the list</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``tl``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| returns the list tail without the first element</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``++``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 25``\ </entry>
                    <entry colname="type">|nbsp| ``[a] List a * List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| list concatenation</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``concat``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a * List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| prefix :token:`op` for list concatenation</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``flatten``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List(List(a)) -> List a``\ </entry>
                    <entry colname="desc">|nbsp| returns the concatenation of the list elements</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``diff``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a * List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| list subtraction:
                        ``diff(``\ *x*\ ``,``\ *y*\ ``)``
                        returns a list containing the elements of
                        *x* that are not in
                        *y*, preserving the order of the
                        elements in *x*</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``member``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] a * List a -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| list membership</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``nth``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a * Nat -> a``\ </entry>
                    <entry colname="desc">|nbsp| ``nth(``\ *x*\ ``,``\ *n*\ ``)`` returns the element at position
                        *n* of list *x*, counting from 0</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``nthTail``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a * Nat -> List a``\ </entry>
                    <entry colname="desc">|nbsp| ``nthTail(``\ *x*\ ``,``\ *n*\ ``)`` returns the
                        tail of list *x*, starting after position
                        *n*, counting from 0</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``sublist``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a * Nat * Nat -> List a``\ </entry>
                    <entry colname="desc">|nbsp| sublist(*x*, *m*, *n*)]] returns the
                        tail of list *x*, from position 
                        *m* up to but not including *n*, counting from 0</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``foldl``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a*b -> b) -> b -> List a -> b``\ </entry>
                    <entry colname="desc">|nbsp| ``foldl``\ *f*\  \ *e*\  \ *x*\ 
                        successively applies function *f* to
                        the elements of list *x* from left to
                        right. The second argument to *f* is
                        initially *e* and at each next step
                        the result of the previous invocation of *f*</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``foldr``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a*b -> b) -> b -> List a -> b``\ </entry>
                    <entry colname="desc">|nbsp| like ``foldl``\ , but the elements of the list are
                        processed from right to left</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``map``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> b) -> List a -> List b``\ </entry>
                    <entry colname="desc">|nbsp| applies function to each element of a list and returns
                        the list consisting of the results</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``mapPartial``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> Option b) -> List a -> List b``\ </entry>
                    <entry colname="desc">|nbsp| like ``map`` but replacing each result ``Some``\ *y*\ 
                        by *y* and deleting ``None`` results.</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``filter``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a -> Bool) -> List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| returns the list of elements satisfying the given predicate</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``rev``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a -> List a``\ </entry>
                    <entry colname="desc">|nbsp| reverse list</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``all``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a -> Bool) -> List a -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true if all elements of the list satisfy
                        the predicate given as first parameter</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``exists``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a -> Bool) -> List a -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| true if some element of the list satisfies
                        the predicate given as first parameter</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``find``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a -> Bool) -> List a -> Option(a)``\ </entry>
                    <entry colname="desc">|nbsp| returns ``Some``\ *x*\  where *x* is the
                        first element in the list (from left to right) for which the
                        given predicate yields true; if no such element exists,
                        ``None`` is returned</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``tabulate``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] Nat * (Nat -> a) -> List a``\ </entry>
                    <entry colname="desc">|nbsp| ``tabulate(``\ *n*\ ``,``\ *f*\ ``)`` returns the list
                        ``[``\ *f*\ ``(0),``\ *f*\ ``(1),`` ... ``,``\ *f*\ ``(``\ *n*\ ``-1)``\ ]</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``firstUpTo``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a -> Bool) -> List a -> Option (a * List a)``\ </entry>
                    <entry colname="desc">|nbsp| returns [[Some(*e*,
                        *x*)]] where
                        *e* is the first element in the list
                        (from left to right) satisfying the given predicate and
                        *x* the initial list segment preceding
                        *e*; if no such element exists,
                        ``None`` is returned</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``splitList``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a -> Bool) -> List a -> Option (List a * a * List a)``\ </entry>
                    <entry colname="desc">|nbsp| returns [[Some(*x*,
                        *e*,
                        *y*)]] where
                        *e* is the first element in the list
                        (from left to right) satisfying the given predicate,
                        *x* the initial list segment preceding
                        *e*, and *y*
                        the list tail following *e*; if no
                        such element exists, ``None`` is returned</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``locationOf``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] List a * List a -> Option (Nat * List a)``\ </entry>
                    <entry colname="desc">|nbsp| [[locationOf(*s*,
                        *t*)]] returns
                        [[Some(*n*,
                        *x*)]] where
                        *n* is the first position in list
                        *t* (counting from from left to right)
                        where list *s* occurs as a contiguous
                        sublist, and *x* the list tail segment
                        following *s* in
                        *t*; if *s*
                        does not occur in *t*, ``None`` is
                        returned</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a * a -> Comparison) -> List a * List a -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| compares two list using the comparison function given as first parameter</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] String -> List String -> String``\ </entry>
                    <entry colname="desc">|nbsp| ``show(``\ *s*\ ``,``\ *x*\ ``)`` returns the element strings
                        in *x* concatenated, with string *s*
                        inserted between any two elements</entry>
                   </row>
                    </tbody>
                   </tgroup>
                  </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  Compare ****************************************************** 

.. COMMENT: <section><title>Compare</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Type</command></term>
                <listitem><para>\ ``type Comparison = | Less | Equal | Greater``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                    <informaltable frame="sides" colsep="1">
                     <tgroup cols="4">
                      <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                      <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                      <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                      <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                      <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                      </thead>
                      <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Comparison * Comparison -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| compares comparison values</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``Comparison -> String``\ </entry>
                    <entry colname="desc">|nbsp| converts comparison value to string</entry>
                   </row>
                      </tbody>
                     </tgroup>
                    </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  Option ****************************************************** 

.. COMMENT: <section><title>Option</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Type</command></term>
                <listitem><para>\ ``type Option a = | Some a | None``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                    <informaltable frame="sides" colsep="1">
                     <tgroup cols="4">
                      <colspec colname="name" colnum="1" colwidth="65"  rowsep="1">
                      <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                      <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                      <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                      <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                      </thead>
                      <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``some``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] a -> Option a``\ </entry>
                    <entry colname="desc">|nbsp| :token:`op` that constructs ``Some``\ *x*\ \ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``none``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] Option a``\ </entry>
                    <entry colname="desc">|nbsp| :token:`op` that constructs ``None``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``some?``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] Option a -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| tests if the parameter is of the form ``Some``\ *x*\ \ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``none?``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] Option a -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| tests if the parameter is ``None``\ </entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``compare``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] (a * a -> Comparison) -> Option a * Option a -> Comparison``\ </entry>
                    <entry colname="desc">|nbsp| returns the result of the comparison of the two optional
                        values, where ``None`` is less than [[Some
                        *x*]] for all
                        *x*; if both optional values are of
                        the form ``Some``\ *x*\ \ , the comparison
                        function given as
                        first parameter is used to compute the result</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``mapOption``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> b) -> Option a -> Option b``\ </entry>
                    <entry colname="desc">|nbsp| applies the function given as first parameter to the
                        optional value if it is ``Some``\ *x*\ \ ,
                        otherwise ``None`` is returned</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``show``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> String) -> Option a -> String``\ </entry>
                    <entry colname="desc">|nbsp| converts optional value to string; if the optional value
                        is ``Some``\ *x*\ \ , it uses the function
                        given as first parameter to convert
                        *x* to a string</entry>
                   </row>
                      </tbody>
                     </tgroup>
                    </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

.. COMMENT:  Functions ****************************************************** 

.. COMMENT: <section><title>Functions</title>
             <para>
              <variablelist>
               <varlistentry>
                <term><command>Types</command></term>
                <listitem><para>\ ``type Injection(a,b)  = ((a -> b) | injective?)``\ </para>
                          <para>\ ``type Surjection(a,b) = ((a -> b) | surjective?)``\ </para>
                          <para>\ ``type Bijection(a,b)  = ((a -> b) | bijective?)``\ </para></listitem>
               </varlistentry>
               <varlistentry>
                <term><command>Ops</command></term>
                <listitem>
                 <para>
                <informaltable frame="sides" colsep="1">
                 <tgroup cols="4">
                  <colspec colname="name" colnum="1" colwidth="50"  rowsep="1">
                  <colspec colname="fxty" colnum="2" colwidth="41"  rowsep="1">
                  <colspec colname="type" colnum="3" colwidth="150" rowsep="1">
                  <colspec colname="desc" colnum="4" colwidth="160" rowsep="1">
                  <thead>
                   <row>
                    <entry colname="name">|nbsp| Name</entry>
                    <entry colname="fxty">|nbsp| Fixity</entry>
                    <entry colname="type">|nbsp| Type</entry>
                    <entry colname="desc">|nbsp| Description</entry>
                   </row>
                  </thead>
                  <tbody>
                   <row>
                    <entry colname="name">|nbsp| ``id``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a] a -> a``\ </entry>
                    <entry colname="desc">|nbsp| identity function</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``o``\ </entry>
                    <entry colname="fxty">|nbsp| ``L 24``\ </entry>
                    <entry colname="type">|nbsp| ``[a,b,c] (b -> c) * (a -> b) -> (a -> c)``\ </entry>
                    <entry colname="desc">|nbsp| function composition</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``injective?``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> b) -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| injectivity predicate; non-constructive</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``surjective?``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> b) -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| surjectivity predicate; non-constructive</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``bijective?``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] (a -> b) -> Bool``\ </entry>
                    <entry colname="desc">|nbsp| bijectivity predicate; non-constructive</entry>
                   </row>
                   <row>
                    <entry colname="name">|nbsp| ``inverse``\ </entry>
                    <entry colname="fxty">|nbsp| </entry>
                    <entry colname="type">|nbsp| ``[a,b] Bijection(a,b) -> Bijection(b,a)``\ </entry>
                    <entry colname="desc">|nbsp| inverts bijective function; non-constructive</entry>
                   </row>
                  </tbody>
                 </tgroup>
                </informaltable>
                 </para>
                </listitem>
               </varlistentry>
              </variablelist>
             </para>
            </section>

