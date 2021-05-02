// var f2 = (tmp) => {
//     var a = null;
//     var m = {
//         "a" : 0, 
//         "b" : 4,
//         "c" : {
//             "tr" : 4
//         }
//     };
//     //m.c.tr = 5;
// }

// m.c.tr = 4;

// var f2 = (tmp) => {
//     var a = 1;
//     var h = {};
//     var d = {};
//     var m = {"a":0, "b": 4,"c":45};
//     if (h == d) {
//         m = {"tr":4};
//     }
//     if(m == h) {
//         a = 5;
//     }
// }

var f2 = (tmp) => {
    if(tmp > 0.0) {
        tmp = 0;
    }
    var a = null;
    if(!a){
        a = 1;
    }
    var m = 3.14
    var k;
    var a = 7;
    var b = 3;
    var d = {a : 1, b:8};
    k = b;
    var s = "ciao";
    if(k == null){
        k = 3;
    }
    if(k) {
        k = 8;
    }
    if(k<2) {
        k = (b+2)*3;
        b = a;
        k = 8;
        k=9;
    } 
    else {
        b = 1;
    }
    if(b>k) {
        k = (b+2)*3;
        b = 0;
        k = 6;
    }
    if(!b){
        b = "aaa";
    }
    if(s == "ciao"){
        s = "abc";
    }
}
