TARGET = main.byte

default: $(TARGET)

hard: $(TARGET)
	./$<

%.byte: $(wildcard *.ml)
	corebuild $@

clean:
	$(RM) -R *.byte *.native _build
