$("body").on("click", ".slider", function () {
    $collapse = $(this).parent().next();
    $collapse.slideToggle(500, function () {
        });

});

$("body").on("click", ".sliderall", function () {
    $content = $(this).parent().next();
    $content.slideToggle(500, function () {
        });

});
