TARGET = main.byte

default: $(TARGET)

hard: $(TARGET)
	cat examples/* | ./$<

%.byte: $(wildcard *.ml)
	corebuild $@

clean:
	$(RM) -R *.byte *.native _build
