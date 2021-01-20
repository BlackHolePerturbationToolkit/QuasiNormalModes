{% include head.html %}

<p>
 <h1 style="display:inline">QuasiNormalModes</h1> <span style="float:right;"><a href="{{ site.github.repository_url }}" class = "code_btn">Get the code!</a></span>
</p>

A Mathematica package for computing quasinormal modes (QNMs) in Schwarzschild and Kerr spacetime. The package introduces a new function
```
QuasiNormalMode[s, l, m, n, a]
```
where  
$s$ - is the spin-weight of the perturbing field  
$l$ - is the multipolar index  
$m$ - is the azimuthal index  
$n$ - is the overtone number  
$a$ - is the black hole spin parameter

Currently the Schwarzschild ($a=0$) case works well. For QNMs in Kerr you are not guaranteed that the mode returned corresponds to the specified overtone number (though often it will).

### Further examples

Additional documentation can be found in the Mathematica Documentation included with the package.

## Authors and contributors

**Conor O'Toole**, Rodrigo Macedo, Tom Stratton, Barry Wardell