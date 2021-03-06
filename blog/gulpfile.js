const gulp        = require('gulp');
var browserSync   = require('browser-sync').create();
const reload      = browserSync.reload;
const sass        = require('gulp-sass');
const concat      = require('gulp-concat');
const plumber     = require('gulp-plumber');

const cssnano     = require('gulp-cssnano');
const uglify      = require('gulp-uglify');
const imagemin    = require('gulp-imagemin');

const child       = require('child_process');
const gutil       = require('gulp-util');
gutil.log         = gutil.noop;

const watch       = require('gulp-watch');
var Vinyl         = require('vinyl');

const scriptFiles = '_js/**/*.js';


var messages = {
  jekyllDev  : 'Running: $ jekyll build for dev',
  jekyllProd : 'Running: $ jekyll build for prod'
};

gulp.task('jekyll-dev', function (done) {
  browserSync.notify(messages.jekyllDev);
  const jekyll = child.spawn( 'jekyll'
                            , ['build', '--incremental']
                            , {stdio: 'inherit'}
                            )
                      .on('close', done);
});

gulp.task('jekyll-rebuild', ['jekyll-dev'], function () {
  browserSync.reload();
});

gulp.task('sass', function(){
  return gulp.src(['_sass/main.scss'])
             .pipe(plumber())
             .pipe(sass({onError: browserSync.notify}))
             .pipe(concat('main.css'))
             .pipe(plumber.stop())
             .pipe(gulp.dest('_site/assets'))
             .pipe(browserSync.reload({stream:true, message: "Sass updated!"}))
             .pipe(gulp.dest('assets'));
});

gulp.task('scripts', function() {
  return gulp.src(scriptFiles)
             .pipe(plumber())
             .pipe(concat('main.js'))
             .pipe(plumber.stop())
             .pipe(gulp.dest('_site/assets'))
             .pipe(browserSync.reload({stream:true}))
             .pipe(gulp.dest('assets'));
});

gulp.task('ipe-images', () => function(){
	return gulp.src('assets/ipe-images/*.png')
          	 .pipe(imagemin())
             .pipe(gulp.dest('_site/assets/ipe-images'))
             .pipe(browserSync.reload())
});

gulp.task('png-images', () => function(){
	return gulp.src('assets/png-images/*.png')
          	 .pipe(imagemin())
          	 .pipe(gulp.dest('_site/assets/png-images'))
});

gulp.task('reload', () => function(){
  return gulp.pipe(browserSync.reload())
});


gulp.task('browser-sync', ['sass', 'scripts', 'jekyll-dev'], function() {
  browserSync.init({ browser: 'chrome'
                   , open: false
                   , files: [ '_site/**']
                   , server: { baseDir: "./_site" }
                   , port: 4000
                  });

  gulp.watch(['_sass/**/*.scss','_sass/*.scss'], ['sass']);
  gulp.watch(['_js/**/*.js'], ['scripts']);
  gulp.watch(['_src/ipe-images/*'], ['ipe-images']);
  gulp.watch(['*.html', '*.md', '_layouts/*.html', '_posts/*'
             , '_includes/*.html', '_drafts/*', '**/*.html'
            ], ['jekyll-rebuild']);

  var latexit = function(obj) {
    plumber();
    var file = new Vinyl();
    file.path = obj.path;
    console.log('*****************************************************************************');
    console.log('[!] Image File ' + file.basename + ' changed!');
    var outputpath = file.base + '/assets/latexit-images/' + file.basename;
    child.spawn( 'cp'
               , [ file.path
                 , outputpath
                 ]
               , { stdio: 'inherit' }
               )
         .on('close', function(){
           console.log("[!] Updated file by copying: " + outputpath);
           console.log('*****************************************************************************');
           reload;
          });
    plumber.stop();
  };

  gulp.watch(['_src/latexit-images/*'])
      .on('add',    latexit )
      .on('change', latexit )
      .on('unlink', function(obj) {
        console.log('[!] File ' + obj.path + ' was removed');
        console.log('*****************************************************************************');
      });

  gulp.watch(['_src/notes/*'])
      .on('change', function(obj) {
      plumber();
      var file = new Vinyl();
      file.path = obj.path;
      console.log('*****************************************************************************');
      console.log('[!] File ' + file.stem + ' changed!');
      // console.log('path:' + file.path);
      // console.log('base:' + file.base);
      // console.log('dirname:'  + file.dirname);
      // console.log('basename:' + file.basename);
      // console.log('extname:' + file.extname);
      // console.log('stem:' + file.stem);
      if ( file.extname == ".md" ){
        var outputpath = file.base + '/_posts/' + file.stem + '.md';
        child.spawn( 'cp'
                   , [ file.path
                     , outputpath
                     ]
                   , { stdio: 'inherit' }
                   )
             .on('close', function(){
               console.log("[!] Updated file by copying: " + outputpath);
               console.log('*****************************************************************************');
               reload;
              });
      }
      if ( file.extname == ".lagda"){
        console.log("[!] Agda File.");
        var outputpath = file.base + '/_posts/' + file.stem + '.md';
        console.log("[!] Waiting for the markdown: " + outputpath);
        // console.log("[!] Generating markdown: " + outputpath);
        // var agda2html = child.spawn( 'agda2html'
        //                           , [ '--link-to-agda-stdlib'
        //                             , '--link-to-local-agda-names'
        //                             , '--use-jekyll=_posts/'
        //                             , '-i' , file.path
        //                             , '-o' , outputpath
        //                             ]
        //                           , {stdio: 'inherit'}
        //                           )
        //                     .on('close', function(){
        //                       console.log("[!] Updated file by agda2html: " + outputpath);
        //                       console.log('*****************************************************************************');
        //                       reload;
        //                     });
      };
      plumber.stop();
      })
      .on('unlink', function(obj) {
      console.log('[!] File ' + obj.path + ' was removed');
      console.log('*****************************************************************************');
      })
      .on('error', function(obj) {
      console.log('[!FATAL] : ' + obj);
      console.log('*****************************************************************************');
      });
  return;
});

// Production

gulp.task('jekyll-prod', function (done) {
  browserSync.notify(messages.jekyllProd);
  return child.spawn('jekyll', ['build'], {stdio: 'inherit'})
              .on('close', done);
});

gulp.task('jekyll-algolia', function (done) {
  return child.spawn('jekyll', ['algolia'], {stdio: 'inherit'})
              .on('close', done);
});

gulp.task('sass-prod', () => {
  return gulp.src(['_sass/main.scss'])
             .pipe(plumber())
             .pipe(sass({onError: browserSync.notify}))
             .pipe(concat('main.css'))
             .pipe(cssnano())
             .pipe(plumber.stop())
             .pipe(gulp.dest('_site/assets'))
             .pipe(browserSync.reload({stream:true}))
             .pipe(gulp.dest('assets'));
});

gulp.task('scripts-prod', function() {
  return gulp.src(scriptFiles)
             .pipe(plumber())
             .pipe(concat('main.js'))
             .pipe(uglify())
             .pipe(plumber.stop())
             .pipe(gulp.dest('_site/assets'))
             .pipe(browserSync.reload({stream:true}))
             .pipe(gulp.dest('assets'));
});

// DEFAULT
gulp.task('default', ['sass'
                     , 'jekyll-dev'
                     , 'browser-sync'
                     ]);

gulp.task('build', ['scripts-prod'
                   , 'sass-prod'
                   , 'jekyll-prod'
                   , 'ipe-images'
                   , 'png-images'
                   , 'jekyll-algolia'
                   ]);
