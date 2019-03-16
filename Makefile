all : 
	coqc Rml.v
	coqc Rml_semantic.v

clean : 
	rm *.glob
	rm *.vo
	rm .*.aux
