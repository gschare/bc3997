/* Collapsible */
let collapsible = document.getElementsByClassName("collapsible");

for (let i=0; i<collapsible.length; i++) {
    collapsible[i].addEventListener("click", () => {
        collapsible[i].classList.toggle("active");
        let content = collapsible[i].nextElementSibling;
        if (content.style.display === "block") {
          content.style.display = "none";
        } else {
          content.style.display = "block";
        }
    });
}

/* Synthesizer */
const MIN_INT = 0;
const MAX_INT = 9;

const Plus  = (x,y) => { return x + y };
const Minus = (x,y) => { return x - y };
const Times = (x,y) => { return x * y };
const Div   = (x,y) => { return Math.floor(x/y) };

const FUNCTIONS = ["Plus", "Minus", "Times", "Div"];
const TERMINALS = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "x"];

let examples = [];
let plist = [TERMINALS]; // Programs of size 1 are just the terminals.

function check(f, x) {
    return eval("((x) => { return " + f + "; })(x)");
}

function grow() {
    let newPrograms = [];
    for (let i=0; i<plist.length; i++) {
        for (let p of plist[i]) {
            // Try wrapping the current program in a new function.
            for (let f of FUNCTIONS) {
                for (let j=0; j<plist.length; j++) {
                    for (let q of plist[j]) {
                        newPrograms.push(f + "(" + p + "," + q + ")");
                    }
                }
            }
        }
    }
    plist.push(newPrograms);
}

function elimEquivalents() {

    for (let i=0; i<plist.length; i++) {
        for (let p of plist[i]) {
            for (let j=0; j<plist.length; j++) {
                for (let q of plist[j]) {
                    if (examples.every((ex) => { return check(p, ex.input) === check(q, ex.input); })) {
                        if (i === j && p !== q) {
                            plist[j] = plist[j].filter(item => item !== q);
                        }
                    }
                }
            }
        }
    }
}

function synthesize() {
    // Try all the most recently created programs.
    for (let size of plist) {
        for (let p of size) {
            if (examples.every((ex) => { return check(p, ex.input) === ex.output; })) {
                return p;
            }
        }
    }
    while (plist.length < 5) {
        console.log(plist);
        for (let p of plist[plist.length-1]) {
            if (examples.every((ex) => { return check(p, ex.input) === ex.output; })) {
                return p;
            }
        }
        grow();
        //elimEquivalents(); // don't do this step
    }
}

function submitForm(that) {
    examples.push({input: parseInt(that.input.value), output: parseInt(that.output.value)});
    // no input sanitation...

    let table = document.getElementById("examples");
    table.innerHTML = table.innerHTML + "<pre>" + that.input.value + " &rarr; " + that.output.value + "</pre>"

    that.reset();

    let f = synthesize();

    let result = document.getElementById("result");
    result.innerHTML = "f(x) = " + f;
}
