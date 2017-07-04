$("body").on("click", ".slider", function () {
    $slider = $(this);
    $collapse = $slider.next();
    $collapse.slideToggle(500, function () {
        });

});

$("body").on("click", ".sliderall", function () {
    $slider = $(this);
    $contentall = $slider.next();
    $contentall.slideToggle(500, function () {
        });

});