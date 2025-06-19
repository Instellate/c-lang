RS_SOURCES := $(wildcard src/*.rs) $(wildcard src/**/*.rs)
RS_BIN := ./target/debug/c-lang

SOURCES := $(wildcard src-c/*.c)
OBJECTS := $(patsubst src-c/%.c,build/%.o,$(SOURCES))
IR_FILES := $(patsubst src-c/%.c,build/%.ll,$(SOURCES))

LIBRARIES := glib-2.0

LDFLAGS = -lc $(shell pkg-config --libs $(LIBRARIES))
CRT1 = $(shell gcc -print-file-name=crt1.o)
CRTI = $(shell gcc -print-file-name=crti.o)
CRTN = $(shell gcc -print-file-name=crtn.o)
LDPATH = $(shell gcc -print-file-name=ld-linux-x86-64.so.2)

build: build/c-lang

build/c-lang: $(OBJECTS) $(IR_FILES)
	$(Linking)
	ld -o $@ -dynamic-linker $(LDPATH) $(CRT1) $(CRTI) $(CRTN) $(OBJECTS) $(LDFLAGS)

build/%.o: src-c/%.c $(RS_BIN)
	$(info Building $<)
	@mkdir -p $(@D)
	$(RS_BIN) $< -o $@

build/%.ll: src-c/%.c $(RS_BIN)
	$(RS_BIN) $< --output-ir $@

$(RS_BIN): $(RS_SOURCES)
	$(info Building compiler)
	@cargo build $(CARGOFLAGS)

clean:
	rm ir ir.o
