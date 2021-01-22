// var d = [1,[[64,128],5],[2,2],{"a":3}];
// var k = {
//     "aaa": "dsagdd",
//     "bbb": "dfggffdg"
// };
// function abc(a) {
//     // function embedded() {
//     //     k = 3;
//     //     return k;
//     // }
//     // var b = {
//     //     "primo": [1,2,3],
//     //     "secondo": {
//     //         "aaa": "dsagdd",
//     //         "bbb": "dfggffdg"
//     //     }
//     // };
//     // var c = {
//     //     "aaa": "dsagdd",
//     //     "bbb": "dfggffdg"
//     // };
//     var d = [1,[4,5],[2,2],{"a":3}];
// }

var f2 = (tmp) => {
    var k = 2;
    var b = 3;
    k = b;
    if(b>k) {
        k = (b+2)*3;
        b = 0;
        k = 6;
    }
    else
        k = 0;
    if(k>b) {
        b = 0;
    }
}

//f2(3);
// console.assert(x == 2);
// abc(4);
// abc.embedded();
