all : 
	coqc Rml.v
	coqc Rml_semantic.v
	coqc pWhileInterp.v

clean : 
	rm *.glob
	rm *.vo
	rm .*.aux
