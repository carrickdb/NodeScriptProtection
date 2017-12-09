const crypto = require('crypto');
const fs = require('fs');


function getHash(str) {
    const hash = crypto.createHash('sha256');
    hash.update(str);
    return hash.digest('hex');
}

var walkSync = function(dir, filelist) {
    var path = path || require('path');
    var fs = fs || require('fs'),
    files = fs.readdirSync(dir);
    filelist = filelist || [];
    files.forEach(function(file) {
        if (fs.statSync(path.join(dir, file)).isDirectory()) {
            filelist = walkSync(path.join(dir, file), filelist);
        }
        else {
            filelist.push(path.join(dir, file));
        }
    });
    return filelist;
};

if (process.argv.length != 3) {
    console.log("Usage: node getHashes.js [app_parent_folder]");
    throw new Error();
}

hashes = ""

filelist = walkSync(__dirname, []);
filelist.forEach(file => {
    re = /\.js$/;
    if (re.test(file)) {
        var source = fs.readFileSync(file)
        var src_hash = getHash(source);
        hashes += src_hash + '\n';
//        console.log(file + " " + src_hash);
    }
})

var app_folder = process.argv[2];
filelist = walkSync(app_folder, []);
filelist.forEach(file => {
    var re = /\.js$/;
    if (re.test(file)) {
        var source = fs.readFileSync(file)
        source = '(function (exports, require, module, __filename, __dirname) { ' + source + '\n});';
        var src_hash = getHash(source);
        hashes += src_hash + '\n';
//        console.log(file + " " + src_hash);
    }
})

hash_file = app_folder + "/src_hashes";
fs.truncate(hash_file, 0, function() {
    fs.writeFile(hash_file, hashes, function (err) {
        if (err) throw err;
    });
});

