const gulp         = require('gulp');
var browserSync    = require('browser-sync').create();
const sass         = require('gulp-sass');
const concat       = require('gulp-concat');

const cssnano      = require('gulp-cssnano');
const uglify       = require('gulp-uglify');
const imagemin     = require('gulp-imagemin');

const child        = require('child_process');
const gutil        = require('gulp-util');

const sassFiles     = '_sass/**/*.?(s)css';
const scriptFiles  = '_js/**/*.js';

var messages = {
  jekyllDev: 'Running: $ jekyll build for dev',
  jekyllProd: 'Running: $ jekyll build for prod'
};

gulp.task('jekyll-dev', function (done) {
  browserSync.notify(messages.jekyllDev);
  const jekyll = child.spawn('jekyll', ['build'], {stdio: 'inherit'})
 .on('close', done);
});

gulp.task('jekyll-rebuild', ['jekyll-dev'], function () {
  browserSync.reload();
});

gulp.task('sass', () => {
  return gulp.src(sassFiles)
        .pipe(sass({onError: browserSync.notify}))
        .pipe(concat('main.css'))
        .pipe(gulp.dest('_site/assets'))
        .pipe(browserSync.reload({stream:true}))
        .pipe(gulp.dest('assets'));
});

gulp.task('scripts', function() {
  return  gulp.src(scriptFiles)
              .pipe(concat('main.js'))
              .pipe(gulp.dest('_site/assets'))
              .pipe(browserSync.reload({stream:true}))
              .pipe(gulp.dest('assets'));
});

gulp.task('browser-sync', ['sass', 'scripts', 'jekyll-dev'], function() {
  browserSync.init({
    browser: 'chrome',
    open: false,
    files: [ '_site/**'],
    server: {
      baseDir: "./_site"
    },
    port: 4000
  });

  gulp.watch(['_sass/**/*.scss','_sass/*.scss'], ['sass']);
  gulp.watch(['_js/**/*.js'], ['scripts']);
  gulp.watch(['src/notes/*.lagda','src/notes/*.md'], ['make']);
  gulp.watch(['*.html', '_layouts/*.html', '_posts/*', '_includes/*.html', '_drafts/*', '**/*.html'], ['jekyll-rebuild']);

});

gulp.task('make', function (){
  var cmd = child.spawn('make', [], {stdio: 'inherit'});
});


gulp.task('ipe-images', () => function(){
	return gulp.src('assets/ipe-images/*.png')
          		.pipe(imagemin())
          		.pipe(gulp.dest('_site/assets/ipe-images'))
});

gulp.task('png-images', () => function(){
	return gulp.src('assets/png-images/*.png')
          		.pipe(imagemin())
          		.pipe(gulp.dest('_site/assets/png-images'))
});

// Production

gulp.task('jekyll-prod', function (done) {
  browserSync.notify(messages.jekyllProd);
  return child.spawn('jekyll', ['build'], {stdio: 'inherit'})
              .on('close', done);
});

gulp.task('sass-prod', () => {
  return gulp.src(sassFiles)
            .pipe(sass({onError: browserSync.notify}))
            .pipe(concat('main.css'))
            .pipe(cssnano())
            .pipe(gulp.dest('_site/assets'))
            .pipe(browserSync.reload({stream:true}))
            .pipe(gulp.dest('assets'));
});

gulp.task('scripts-prod', function() {
  return gulp.src(scriptFiles)
             .pipe(concat('main.js'))
             .pipe(uglify())
             .pipe(gulp.dest('_site/assets'))
             .pipe(browserSync.reload({stream:true}))
             .pipe(gulp.dest('assets'));
});

// DEFAULT
gulp.task('default', ['sass', 'jekyll-dev', 'browser-sync']);

gulp.task('build', ['scripts-prod', 'sass-prod', 'jekyll-prod', 'ipe-images', 'png-images']);
