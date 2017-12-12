const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

function getHash(str) {
    const hash = crypto.createHash('sha256');
    hash.update(str);
    return hash.digest('hex');
}

var walkSync = function(dir, filelist) {
    files = fs.readdirSync(dir);
    filelist = filelist || [];
    files.forEach(function(file) {
        var curr_path = path.join(dir, file);
        if (fs.existsSync(curr_path) && fs.statSync(curr_path).isDirectory()) {
            filelist = walkSync(curr_path, filelist);
        }
        else {
            filelist.push(path.join(dir, file));
        }
    });
    return filelist;
};

if (process.argv.length != 3) {
    console.log("Usage: node getHashes.js [app_folder]");
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

var parent_dir = app_folder.substring(0, app_folder.lastIndexOf("\/")+1);
var hash_file = parent_dir + "src_hashes";
fs.writeFile(hash_file, hashes, { flag: 'w' }, function (err) {
    if (err) throw err;
});
fs.chmodSync(hash_file, 0444);
console.log("File of hashes successfully created.");

