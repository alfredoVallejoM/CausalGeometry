# Aritmética causal y restricción correlativa

## 0. Alcance

Este documento fija el núcleo matemático autónomo que debe formalizarse antes
de las realizaciones ECIA, Wilderber, RH/BSD/Langlands u otras capas
científicas. No incluye la campaña separada del motivo generativo dinámico.

La tesis fundamental es:

\[
\boxed{
\text{causalidad hacia delante}
\quad\dashv\quad
\text{restricción correlativa hacia atrás}.
}
\]

La aritmética causal no es la aritmética ordinaria con metadatos. Su objeto
básico es un endodiario causal y sus operaciones conservan composición,
orden, parentización, alternativas, restricciones y genealogía antes de toda
decategorificación.

## 1. Números causales

Para una frontera \(A\),

\[
CNum(A)=End_{\mathbf{Cau}}(A).
\]

Un número causal \(X:A\rightsquigarrow A\) puede componerse secuencialmente con
otro número causal. La composición

\[
X\circ Y
\]

es la multiplicación causal primaria.

No se impone por definición:
- conmutatividad;
- asociatividad estricta en vez de coherente;
- distributividad simétrica;
- cancelación;
- existencia de inversos.

La suma causal se introduce en una envolvente aditiva separada. El producto
paralelo es otra operación. La acción sobre historias es otra operación. El
cierre/sombra cíclica es otra operación.

## 2. Órdenes causales y dominios de posibilidades

A cada frontera \(A\) se puede asociar, cuando el modelo lo soporte, un
preorden o retículo

\[
\mathsf{Poss}(A)
\]

de posibilidades/admisibilidades/restricciones. El orden se lee como inclusión
de información o refinamiento según el modelo, pero la convención debe fijarse
una vez por dominio.

Para un proceso causal

\[
h:A\rightsquigarrow B
\]

la **extensión causal**

\[
h_!:\mathsf{Poss}(A)\to\mathsf{Poss}(B)
\]

transporta posibilidades hacia delante.

La **restricción correlativa**

\[
h^*:\mathsf{Poss}(B)\to\mathsf{Poss}(A)
\]

transporta condiciones/admisibilidad hacia atrás.

La ley fundamental es la adjunción posetal

\[
\boxed{
h_!P\le Q
\iff
P\le h^*Q.
}
\]

Interpretación: \(h^*Q\) es la mayor posibilidad inicial cuya evolución por
\(h\) cabe dentro de \(Q\).

## 3. Por qué se llama correlativa

La pareja \((P,Q)\) está correlacionada por \(h\) cuando

\[
h_!P\le Q,
\]

equivalentemente

\[
P\le h^*Q.
\]

Así la restricción no es una mera inversión de flecha: reconstruye en el
origen la condición máxima compatible con una condición en el destino.

Esta noción debe mantenerse distinta de:

\[
h^*\neq h^\dagger\neq h^\vee.
\]

- \(h^\dagger\): reversión/daga del proceso;
- \(h^\vee\): dual algebraico/lineal cuando exista;
- \(h^*\): adjunto derecho ordenado de la extensión causal.

En realizaciones geométricas, un pullback puede realizar \(h^*\), pero no lo
define universalmente.

## 4. Unidad, counidad, clausura e interior

La adjunción da automáticamente

\[
P\le h^*h_!P
\]

y

\[
h_!h^*Q\le Q.
\]

Definimos la clausura correlativa

\[
C_h=h^*h_!
\]

y el interior realizable

\[
I_h=h_!h^*.
\]

En posets apropiados:

\[
C_h^2=C_h,
\qquad
I_h^2=I_h.
\]

Los puntos fijos de \(C_h\) son posibilidades ya saturadas respecto al futuro
representado por \(h\). Los puntos fijos de \(I_h\) son condiciones del destino
totalmente realizables desde el origen.

Esta estructura produce una memoria/cierre puramente matemático sin introducir
la campaña separada del motivo generativo.

## 5. Functorialidad

Para

\[
A\xrightarrow h B\xrightarrow g C,
\]

debe cumplirse

\[
(g\circ h)_!
=
g_!\circ h_!,
\]

\[
(g\circ h)^*
=
h^*\circ g^*.
\]

Por tanto la extensión es covariante y la restricción correlativa
contravariante.

Para la identidad:

\[
(id_A)_!=id,
\qquad
(id_A)^*=id.
\]

Cuadrados causales que satisfagan las hipótesis adecuadas pueden además
satisfacer condiciones Beck--Chevalley. Esto es una propiedad posterior, no
un axioma universal.

## 6. Restricción interna de la multiplicación causal

En un dominio de números causales enriquecido sobre un preorden, fijemos
\(X\). La multiplicación izquierda

\[
L_X(Y)=X\circ Y
\]

puede admitir un adjunto derecho. Lo denotamos

\[
X\backslash Z.
\]

Su ley es

\[
\boxed{
X\circ Y\preceq Z
\iff
Y\preceq X\backslash Z.
}
\]

Análogamente, si la multiplicación derecha admite adjunto derecho:

\[
\boxed{
Y\circ X\preceq Z
\iff
Y\preceq Z/X.
}
\]

Los dos residuos se mantienen separados en el caso no conmutativo.

Estos residuos son la versión aritmética interna de la restricción
correlativa.

## 7. División causal sin inversos

En aritmética ordinaria, dividir por \(x\) suele exigir un inverso o una
condición de divisibilidad.

La residuación causal da siempre, cuando existe el adjunto, el **máximo
candidato permitido**:

\[
X\backslash Z.
\]

Tenemos la counidad

\[
X\circ(X\backslash Z)\preceq Z.
\]

Hay división exacta precisamente cuando esta desigualdad se satura en el nivel
de equivalencia fijado:

\[
X\circ(X\backslash Z)\simeq Z.
\]

Esto distingue:
- residuo/restricción;
- división exacta;
- inversa multiplicativa;
- dagger.

En un sector invertible compatible,

\[
X\backslash Z\simeq X^{-1}\circ Z,
\]

pero ésta es una consecuencia especial, no la definición general.

## 8. Divisibilidad

Definimos divisibilidad izquierda:

\[
X\mid_L Z
\iff
\exists Y,\quad X\circ Y\simeq Z.
\]

Si existe residuación, la búsqueda de \(Y\) tiene un candidato canónico:

\[
Y_{\max}=X\backslash Z.
\]

Así:

\[
X\mid_L Z
\]

puede comprobarse mediante la saturación de la counidad:

\[
X\circ(X\backslash Z)\simeq Z.
\]

Análogamente para divisibilidad derecha.

La sombra clásica debe satisfacer

\[
X\mid_L Z\Rightarrow \chi(X)\mid\chi(Z),
\]

sin exigir el recíproco en el nivel causal.

## 9. GCD y LCM

En el preorden de divisibilidad, cuando existen los objetos universales,

\[
\gcd_C(X,Y)
\]

es el mayor divisor causal común y

\[
\operatorname{lcm}_C(X,Y)
\]

el menor múltiplo causal común.

En dominios reticulares apropiados estos son meet/join del orden de
divisibilidad.

La realización clásica debe demostrar, no asumir,

\[
\chi(\gcd_C(X,Y))
=
\gcd(\chi X,\chi Y),
\]

\[
\chi(\operatorname{lcm}_C(X,Y))
=
\operatorname{lcm}(\chi X,\chi Y).
\]

Las realizaciones Tate pueden convertir estas operaciones en
intersección/suma de retículas.

## 10. Primalidad causal

Se mantienen separadas tres nociones:

1. **indecomponibilidad composicional**:
   \(P\simeq X\circ Y\) fuerza una unidad;
2. **primitividad cíclica**:
   \(Sh(P)\) no es una potencia propia;
3. **dirección aritmética irreducible**:
   la sombra genera una única dirección primaria.

El objetivo no es identificarlas por definición sino demostrar comparadores
en dominios aritméticos:

\[
\operatorname{Prime}_C(P)
\Longrightarrow
\operatorname{Primitive}(Sh(P))
\Longrightarrow
\chi(P)\text{ primo},
\]

y estudiar cuándo las implicaciones son equivalencias.

## 11. Perfil primo derivado

El perfil

\[
\nu(X)=\sum_P v_P(X)[P]
\]

debe derivarse de la factorización/restricción causal cuando sea posible.

Para una dirección causal primaria \(P\), definimos la profundidad

\[
v_P(X)
=
\sup\{r:P^r\mid_C X\}
\]

en el dominio donde la supremacía sea finita/decidible.

Mediante residuación:

\[
P^r\mid_C X
\]

se estudia por

\[
P^r\circ(P^r\backslash X)\simeq X.
\]

La valoración clásica \(v_p\) será la sombra de \(v_P\) cuando
\(\chi(P)=p\).

## 12. Longitud y norma

Dada una norma aritmética \(N(P)\) sobre primitivas:

\[
L_C(X)
=
\sum_P v_P(X)\log N(P).
\]

Cuando el teorema de sombra está disponible,

\[
L_C(X)=\log\chi(X)
\]

en el sector positivo.

La longitud se deriva de las profundidades causales y no se identifica con
energía operatorial hasta disponer del comparador correspondiente.

## 13. Torres primarias y completación

Una dirección causal primaria \(P\) induce niveles:

\[
P,\;P^2,\;P^3,\ldots
\]

y cocientes/restricciones de profundidad \(r\).

Un sistema primario finito

\[
A_1\leftarrow A_2\leftarrow\cdots
\]

produce una completación:

\[
\widehat A_P=\varprojlim_rA_r.
\]

En la realización clásica de \(P\) con \(\chi(P)=p\):

\[
A_r\simeq\mathbb Z/p^r\mathbb Z
\]

y

\[
\widehat A_P\simeq\mathbb Z_p.
\]

Un elemento \(p\)-ádico es así una historia coherente a través de todas las
restricciones primarias.

## 14. Ultramétrica como profundidad de correlación

Para dos historias completadas \(x,y\), sea

\[
d_P(x,y)
=
\sup\{r:x|_r=y|_r\}.
\]

La realización local asigna

\[
|x-y|_P
=
N(P)^{-d_P(x,y)}.
\]

Por tanto la ultramétrica es la sombra numérica de una profundidad de
correlación/restricción compartida.

## 15. Extensiones residuales \(q=p^f\)

Una dirección local puede poseer cuerpo residual de cardinal

\[
q=p^f.
\]

La teoría causal debe separar:
- la dirección prima \(p\);
- el grado residual \(f\);
- el cardinal \(q\);
- el uniformizador;
- el parámetro Tate \(q_T\).

Una torre con cardinales \(q^r\) y leyes locales adecuadas puede realizar

\[
\mathcal O_K/\pi^r
\]

y su límite \(\mathcal O_K\).

Esto es una realización enriquecida de la estructura causal primaria, no una
nueva noción de número causal.

## 16. CRT e independencia causal

Para factores primarios independientes, la combinación paralela de canales
de restricción debe compararse con el producto chino:

\[
\mathbb Z/n\mathbb Z
\simeq
\prod_{p^r\parallel n}\mathbb Z/p^r\mathbb Z.
\]

El teorema causal correspondiente debe formular una descomposición de un
sistema de restricciones global en canales primarios independientes y probar
que la realización clásica recupera CRT.

## 17. Incidencia, Möbius y convolución de Dirichlet

La categoría/preorden de factorizaciones de un número causal tiene intervalos
de divisibilidad. En sectores finitos, su álgebra de incidencia admite una
función de Möbius.

La inversión de Möbius separa:
- iteraciones de primitivas;
- factores de divisibilidad;
- conteos acumulados de datos primarios.

La convolución de incidencia debe realizar la convolución de Dirichlet tras
decategorificación:

\[
(f*g)(n)
=
\sum_{d\mid n}f(d)g(n/d).
\]

Así Möbius/Dirichlet son sombras de la combinatoria de restricciones y
factorizaciones causales.

## 18. Ideales, filtros y aritmética lógica

Un subconjunto causal cerrado bajo extensión/multiplicación apropiada puede
modelar un ideal; uno cerrado bajo restricción puede modelar una condición
local o filtro.

En dominios completos/residuados, la operación

\[
X\Rightarrow Z:=X\backslash Z
\]

actúa como implicación residual. En sectores con las hipótesis adecuadas esto
conduce a estructuras de Heyting/quantale/residuated lattice.

Estas estructuras son consecuencias algebraicas opcionales, no axiomas del
núcleo.

## 19. Localización

La restricción correlativa proporciona una noción de división parcial antes de
invertir elementos. Una localización genuina se construye sólo cuando existen
las condiciones universales necesarias (conmutativas u Ore en el caso
no conmutativo).

La relación conceptual es:

\[
\text{residuación}
\to
\text{división exacta}
\to
\text{localización}
\to
\text{fracciones}.
\]

No deben invertirse esos pasos.

## 20. Suma y números con signo

La suma causal se construye en una envolvente aditiva separada:

\[
X\oplus Y.
\]

La completación de Grothendieck proporciona un sector firmado cuando las
hipótesis monoidales lo permiten.

La sombra debe recuperar:

\[
\chi_+(X\oplus Y)=\chi_+(X)+\chi_+(Y)
\]

sólo en la realización aditiva declarada.

La multiplicación causal y la suma aditiva siguen siendo operaciones
diferentes.

## 21. Aritmética clásica como sombra

La realización clásica debe demostrar:

\[
CNum_{\mathrm{arith}}
\longrightarrow
\mathbb N,\mathbb Z,\mathbb Q
\]

con preservación de las operaciones en su dominio.

La secuencia completa esperada es:

\[
\boxed{
\begin{aligned}
&\text{historias y composición}\\
&\downarrow\\
&\text{factorización y restricción correlativa}\\
&\downarrow\\
&\text{primitivas y profundidades}\\
&\downarrow\\
&\text{valuaciones y canales primarios}\\
&\downarrow\\
&\text{completaciones/localizaciones}\\
&\downarrow\\
&\text{sombra clásica}.
\end{aligned}}
\]

Así el perfil primo ya no es una pieza primitiva arbitraria.

## 22. Consecuencias para las realizaciones posteriores

### Grafos

Los grafos aritméticos son realizaciones de historias, composición,
restricciones y primitivas.

### Wilderber

El pullback geométrico

\[
\phi^*
\]

es una realización concreta de la restricción correlativa \(h^*\). La
extensión causal asociada realiza la dirección covariante correspondiente.

### ECIA

Una endocorrespondencia estructural es una realización categórica del número
causal. La sombra, Morita, Tate, cyclicity y realizaciones operatoriales se
organizan sobre ese origen.

### Galois/Hecke/Langlands

Frobenius, Hecke, Hashimoto y otros operadores locales se buscarán como
realizaciones de una misma endocorrespondencia causal primaria.

### Local-global

Las restricciones a lugares \(v\) son instancias de la polaridad causal
global/local. La fibra de compatibilidad produce el patrón que después puede
realizar Selmer/Sha.

## 23. Frontera

Nada en esta teoría afirma por sí solo:
- que todo causal prime sea un primo clásico;
- que todo residuo exista;
- que toda hom-categoría sea un quantale;
- que todo \(p\)-ádico sea reconstruible sin hipótesis adicionales;
- que la realización Galois y la automorfa sean equivalentes;
- RH, BSD, Langlands general o sus conjeturas de valores especiales.

El objetivo del núcleo es producir los objetos y comparadores que permitan
formular y atacar esas afirmaciones sin circularidad.
